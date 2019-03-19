#![allow(clippy::len_without_is_empty)]

use std::marker::PhantomData;

// Reexport here, so we don't depend on merkle_light directly in other places.
use merkle_light::hash::Algorithm;
use merkle_light::merkle;
use merkle_light::merkle::VecStore;
use merkle_light::proof;
use pairing::bls12_381::Fr;

use memmap::MmapMut;
use merkle_light::merkle::{Element, Store};
use rand;
use std::env;
use std::fs;
use std::fs::File;
use std::fs::OpenOptions;
use std::io;
use std::ops;
use std::path::PathBuf;
use tempfile::tempfile;

use crate::hasher::{Domain, Hasher};
use crate::SP_LOG;

// `mmap`ed `MerkleTree` (replacing the previously `Vec`-backed
// `MerkleTree`, now encapsulated in `merkle::VecStore` and exposed
// as `VecMerkleTree`).
pub type MerkleTree<T, A> = merkle::MerkleTree<T, A, DiskMmapStore<T>>;
pub type VecMerkleTree<T, A> = merkle::MerkleTree<T, A, VecStore<T>>;

/// Representation of a merkle proof.
/// Each element in the `path` vector consists of a tuple `(hash, is_right)`, with `hash` being the the hash of the node at the current level and `is_right` a boolean indicating if the path is taking the right path.
/// The first element is the hash of leaf itself, and the last is the root hash.
#[derive(Default, Debug, Clone, Serialize, Deserialize)]
pub struct MerkleProof<H: Hasher> {
    pub root: H::Domain,
    path: Vec<(H::Domain, bool)>,
    leaf: H::Domain,

    #[serde(skip)]
    _h: PhantomData<H>,
}

pub fn make_proof_for_test<H: Hasher>(
    root: H::Domain,
    leaf: H::Domain,
    path: Vec<(H::Domain, bool)>,
) -> MerkleProof<H> {
    MerkleProof {
        path,
        root,
        leaf,
        _h: PhantomData,
    }
}

impl<H: Hasher> MerkleProof<H> {
    pub fn new(n: usize) -> MerkleProof<H> {
        let mut m = MerkleProof::default();
        m.path = vec![(Default::default(), false); n];

        m
    }

    pub fn new_from_proof(p: &proof::Proof<H::Domain>) -> MerkleProof<H> {
        MerkleProof {
            path: p
                .lemma()
                .iter()
                .skip(1)
                .zip(p.path().iter())
                .map(|(hash, is_left)| (*hash, !is_left))
                .collect::<Vec<_>>(),
            root: p.root(),
            leaf: p.item(),
            _h: PhantomData,
        }
    }

    /// Convert the merkle path into the format expected by the circuits, which is a vector of options of the tuples.
    /// This does __not__ include the root and the leaf.
    pub fn as_options(&self) -> Vec<Option<(Fr, bool)>> {
        self.path
            .iter()
            .map(|v| Some((v.0.into(), v.1)))
            .collect::<Vec<_>>()
    }

    pub fn as_pairs(&self) -> Vec<(Fr, bool)> {
        self.path
            .iter()
            .map(|v| (v.0.into(), v.1))
            .collect::<Vec<_>>()
    }

    /// Validates the MerkleProof and that it corresponds to the supplied node.
    pub fn validate(&self, node: usize) -> bool {
        let mut a = H::Function::default();

        if path_index(&self.path) != node {
            return false;
        }

        self.root()
            == &(0..self.path.len()).fold(self.leaf, |h, i| {
                a.reset();
                let is_right = self.path[i].1;

                let (left, right) = if is_right {
                    (self.path[i].0, h)
                } else {
                    (h, self.path[i].0)
                };

                a.node(left, right, i)
            })
    }

    /// Validates that the data hashes to the leaf of the merkle path.
    pub fn validate_data(&self, data: &[u8]) -> bool {
        self.leaf().into_bytes() == data
    }

    /// Returns the hash of leaf that this MerkleProof represents.
    pub fn leaf(&self) -> &H::Domain {
        &self.leaf
    }

    /// Returns the root hash
    pub fn root(&self) -> &H::Domain {
        &self.root
    }

    /// Returns the length of the proof. That is all path elements plus 1 for the
    /// leaf and 1 for the root.
    pub fn len(&self) -> usize {
        self.path.len() + 2
    }

    /// Serialize into bytes.
    /// TODO: probably improve
    pub fn serialize(&self) -> Vec<u8> {
        let mut out = Vec::new();

        for (hash, is_right) in &self.path {
            out.extend(hash.serialize());
            out.push(*is_right as u8);
        }
        out.extend(self.leaf().serialize());
        out.extend(self.root().serialize());

        out
    }

    pub fn path(&self) -> &Vec<(H::Domain, bool)> {
        &self.path
    }
}

fn path_index<T: Domain>(path: &[(T, bool)]) -> usize {
    path.iter().rev().fold(0, |acc, (_, is_right)| {
        (acc << 1) + if *is_right { 1 } else { 0 }
    })
}

// File-mapping version of `MmapStore`. `INTERNAL_TREE_NAME` is used internally
// to set the file name (to label trees with the number of the corresponding
// layer they belong to) and `DISK_BACKED_MMAP_TREE_DIR` is set externally by
// the user to define the directory where the files will be created. (If one
// of these is not set we just create a random file that will be removed after
// `DiskMmapStore` is dropped).
//
// FIXME: Copied from `MmapStore`, needs to be integrated into
//  `merkle_light::merkle`. The only difference is in the `Store::new()`
//  method which creates a file mapping (instead of an anonymous one).
//
// FIXME: `DISK_BACKED_MMAP_TREE_DIR` is being manually set in local
//  tests.
#[derive(Debug)]
pub struct DiskMmapStore<E: Element> {
    store: MmapMut,
    len: usize,
    _e: PhantomData<E>,
    file: File,
    // We need to save the `File` in case we're creating a `tempfile()`
    // otherwise it will get cleaned after we return from `new()`.
    // FIXME: Check this (at least that was the case for `tempdir()`).
}

impl<E: Element> ops::Deref for DiskMmapStore<E> {
    type Target = [E];

    fn deref(&self) -> &Self::Target {
        unimplemented!()
    }
}

impl<E: Element> Store<E> for DiskMmapStore<E> {
    #[allow(unsafe_code)]
    fn new(size: usize) -> Self {
        let byte_len = E::byte_len() * size;

        let file: File = if env::var("INTERNAL_TREE_NAME").is_ok()
            && env::var("DISK_BACKED_MMAP_TREE_DIR").is_ok()
        {
            let trees_dir = PathBuf::from(env::var("DISK_BACKED_MMAP_TREE_DIR").unwrap());

            // Try to create `trees_dir`, ignore the error if `AlreadyExists`.
            if let Some(create_error) = fs::create_dir(&trees_dir).err() {
                if create_error.kind() != io::ErrorKind::AlreadyExists {
                    panic!(create_error);
                }
            }

            let tree_name = env::var("INTERNAL_TREE_NAME").unwrap();

            let tree_name = format!("{}-{}", tree_name, rand::random::<u32>());
            // FIXME: The user of `DISK_BACKED_MMAP_TREE_DIR` should figure out
            // how to manage this directory, for now we create every file with
            // a different random number, the problem being that tests now do
            // replications many times in the same run so they end up reusing
            // the same files with invalid (old) data.

            let tree_path = &trees_dir.join(&tree_name);

            info!(SP_LOG, "creating tree mmap-file"; "path" => &tree_path.to_str());

            OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .open(&tree_path)
                .unwrap()
        } else {
            // We don't know which layer this is (`INTERNAL_TREE_NAME`) or we
            // don't know where to save it (`DISK_BACKED_MMAP_TREE_DIR`), just
            // create *any* temporary file.
            tempfile().unwrap()
        };

        file.set_len(byte_len as u64).unwrap();

        DiskMmapStore {
            store: unsafe { MmapMut::map_mut(&file).unwrap() },
            len: 0,
            _e: Default::default(),
            file,
        }
    }

    fn new_from_slice(size: usize, data: &[u8]) -> Self {
        assert_eq!(data.len() % E::byte_len(), 0);

        let mut res = Self::new(size);

        let end = data.len();
        res.store[..end].copy_from_slice(data);
        res.len = data.len() / E::byte_len();

        res
    }

    fn write_at(&mut self, el: E, i: usize) {
        let b = E::byte_len();
        self.store[i * b..(i + 1) * b].copy_from_slice(el.as_ref());
        self.len += 1;
    }

    fn read_at(&self, i: usize) -> E {
        let b = E::byte_len();
        let start = i * b;
        let end = (i + 1) * b;
        let len = self.len * b;
        assert!(start < len, "start out of range {} >= {}", start, len);
        assert!(end <= len, "end out of range {} > {}", end, len);

        E::from_slice(&self.store[start..end])
    }

    fn read_range(&self, r: ops::Range<usize>) -> Vec<E> {
        let b = E::byte_len();
        let start = r.start * b;
        let end = r.end * b;
        let len = self.len * b;
        assert!(start < len, "start out of range {} >= {}", start, len);
        assert!(end <= len, "end out of range {} > {}", end, len);

        self.store[start..end]
            .chunks(b)
            .map(E::from_slice)
            .collect()
    }

    fn len(&self) -> usize {
        self.len
    }

    fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn push(&mut self, el: E) {
        let l = self.len;
        assert!(
            (l + 1) * E::byte_len() <= self.store.len(),
            "not enough space"
        );

        self.write_at(el, l);
    }
}

impl<E: Element> AsRef<[u8]> for DiskMmapStore<E> {
    fn as_ref(&self) -> &[u8] {
        &self.store
    }
}

impl<E: Element> Clone for DiskMmapStore<E> {
    fn clone(&self) -> DiskMmapStore<E> {
        DiskMmapStore::new_from_slice(
            self.store.len() / E::byte_len(),
            &self.store[..(self.len() * E::byte_len())],
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::{self, Rng};
    use std::io::Write;

    use crate::drgraph::new_seed;
    use crate::drgraph::{BucketGraph, Graph};
    use crate::hasher::{Blake2sHasher, PedersenHasher, Sha256Hasher};

    fn merklepath<H: Hasher>() {
        let g = BucketGraph::<H>::new(10, 5, 0, new_seed());
        let mut rng = rand::thread_rng();
        let node_size = 32;
        let mut data = Vec::new();
        for _ in 0..10 {
            let elt: H::Domain = rng.gen();
            let bytes = H::Domain::into_bytes(&elt);
            data.write(&bytes).unwrap();
        }

        let tree = g.merkle_tree(data.as_slice()).unwrap();
        for i in 0..10 {
            let proof = tree.gen_proof(i);

            assert!(proof.validate::<H::Function>());
            let len = proof.lemma().len();
            let mp = MerkleProof::<H>::new_from_proof(&proof);

            assert_eq!(mp.len(), len);

            assert!(mp.validate(i), "failed to validate valid merkle path");
            let data_slice = &data[i * node_size..(i + 1) * node_size].to_vec();
            assert!(
                mp.validate_data(data_slice),
                "failed to validate valid data"
            );
        }
    }

    #[test]
    fn merklepath_pedersen() {
        merklepath::<PedersenHasher>();
    }

    #[test]
    fn merklepath_sha256() {
        merklepath::<Sha256Hasher>();
    }

    #[test]
    fn merklepath_blake2s() {
        merklepath::<Blake2sHasher>();
    }
}
