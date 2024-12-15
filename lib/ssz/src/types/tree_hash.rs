use std::backtrace::Backtrace;

use typenum::Unsigned;

use crate::{
    tree_hash::{Hash256, MerkleHasher, TreeHashType, BYTES_PER_CHUNK},
    Ssz,
};

/// A helper function providing common functionality between the `TreeHash` implementations for
/// `Vector` and `List`.
pub fn vec_tree_hash_root<T, N>(vec: &[T]) -> Hash256
where
    T: Ssz,
    N: Unsigned,
{
    //println!("ssz vec_tree_hash_root");
    //println!("Backtrace:\n{:?}", Backtrace::capture());

    match T::TREE_HASH_TYPE {
        TreeHashType::Basic { size } => {
            //println!("ssz vec_tree_hash_root TreeHashType::Basic");
            //println!("size: {}", size);
            //println!("vec.len(): {}", vec.len());
            let leaves = chunk_count_basic_list_or_vector::<N>(size);
            //println!("leaves: {}", leaves);
            let mut hasher = MerkleHasher::with_leaves(leaves);

            for item in vec {
                hasher
                    .write(&item.tree_hash_root()[..(size as usize)])
                    .expect("ssz::types variable vec should not contain more elements than max");
            }

            let res = hasher
                .finish()
                .expect("ssz::types variable vec should not have a remaining buffer");
            //println!("res: {:?}", res);
            println!("vec_tree_hash_root res hex: {:?}", serde_utils::to_hex(res));

            res
        }
        TreeHashType::Container | TreeHashType::List | TreeHashType::Vector => {
            println!("ssz vec_tree_hash_root TreeHashType::Container | TreeHashType::List | TreeHashType::Vector");
            let mut hasher = MerkleHasher::with_leaves(N::USIZE);

            for item in vec {
                hasher
                    .write(&item.tree_hash_root())
                    .expect("ssz::types vec should not contain more elements than max");
            }

            hasher
                .finish()
                .expect("ssz::types vec should not have a remaining buffer")
        }
    }
}

/// Corresponds to `chunk_count(type)` definition for `List[B, N]` and `Vector[B, N]` from [the spec](https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md#merkleization).
#[inline]
fn chunk_count_basic_list_or_vector<N>(size: u8) -> usize
where
    N: Unsigned,
{
    (N::USIZE * (size as usize) + 31) / 32_usize
}

/// A helper function providing common functionality for finding the Merkle root of some bytes that
/// represent a bitfield.
#[must_use]
pub fn bitfield_bytes_tree_hash_root<N: Unsigned>(bytes: &[u8]) -> Hash256 {
    let byte_size = (N::USIZE + 7) / 8;
    let leaf_count = (byte_size + BYTES_PER_CHUNK - 1) / BYTES_PER_CHUNK;

    let mut hasher = MerkleHasher::with_leaves(leaf_count);

    hasher
        .write(bytes)
        .expect("bitfield should not exceed tree hash leaf limit");

    hasher
        .finish()
        .expect("bitfield tree hash buffer should not exceed leaf limit")
}
