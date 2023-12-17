use anyhow::{anyhow, Result};
use hex_literal::hex;
use num_bigint::{BigUint, ToBigUint};
use num_traits::Num;
use sha3::{
    digest::generic_array::{typenum::U32, GenericArray},
    Digest, Sha3_256,
};

/// Nodes in Merkle tree are represented as 32-byte (256 bit) arrays as we are using SHA3-256.
type Node = GenericArray<u8, U32>;

/// Representation of Merkle tree.
///
/// It is simplified because it is perfect binary tree, meaning all its nodes with exactly two
/// children, and all leaf nodes at the same level.
pub struct MerkleTree {
    nodes: Vec<Node>,
}

/// Direction representation for tree traversal.
#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum Direction {
    Left,
    Right,
}

impl MerkleTree {
    /// Creates new Merkle tree with given depth and initial leaves. Since it is represented as a
    /// perfect binary tree, there are (2^depth leaves - 1) leaves created in total.
    pub fn new(depth: usize, initial_leaf: Node) -> Result<Self> {
        if depth == 0 {
            return Err(anyhow!("Depth must be greater than zero"));
        }
        let mut tree = Self {
            nodes: vec![initial_leaf; (1 << depth) - 1],
        };
        let mut cur_hash = initial_leaf;
        for cur_depth in (0..depth - 1).rev() {
            let vec_to_hash = [cur_hash.as_slice(), cur_hash.as_slice()].concat();
            // notice we have log(tree.nodes.len()) SHA3 calls in total
            let new_hash = Sha3_256::digest(&vec_to_hash);
            let mut index = Self::depth_and_offset_to_index(cur_depth, 0)?;
            for _ in 0..(1 << cur_depth) {
                tree.nodes[index] = new_hash;
                index += 1;
            }
            cur_hash = new_hash;
        }
        Ok(tree)
    }

    /// Calculate depth of the Merkle tree.
    pub fn depth(&self) -> usize {
        let n = self.nodes.len() + 1;
        assert!(
            n.is_power_of_two(),
            "Number of nodes {n} is not a power of two"
        );
        n.ilog2() as usize
    }

    /// Convert depth and offset (both indexed from 0) to index of the node in the array.
    pub fn depth_and_offset_to_index(depth: usize, offset: usize) -> Result<usize> {
        let pow = 1 << depth;
        if offset >= pow {
            Err(anyhow!(
                "Max offset for depth {} is {} ({} was given)",
                depth,
                pow - 1,
                offset
            ))
        } else {
            Ok(offset + pow - 1)
        }
    }

    /// Convert index of the node in the array to depth and offset (both indexed from 0).
    pub const fn index_to_depth_and_offset(index: usize) -> (usize, usize) {
        let tmp = index + 1;
        let depth = tmp.ilog2() as usize;
        let offset = tmp - (1 << depth);
        (depth, offset)
    }

    /// Convert index of the node in the array to index of its parent. Assume parent of the root is
    /// the root.
    pub const fn index_of_parent(index: usize) -> usize {
        (((index as isize) - 1) / 2) as usize
    }

    /// Convert index of the node in the array to index of its leftmost child. If node has no
    /// children its leftmost child is itself.
    pub fn leftmost_index(&self, index: usize) -> Result<usize> {
        if index >= self.nodes.len() {
            Err(anyhow!(
                "Index {} out of bounds (max allowed index is {})",
                index,
                self.nodes.len() - 1
            ))
        } else {
            let (depth, _offset) = Self::index_to_depth_and_offset(index);
            let delta = self.depth() - depth - 1;
            Ok((1 << delta) * (index + 1) - 1)
        }
    }

    /// Get root of the Merkle tree. This implementation of Merkle tree has always at least one
    /// node.
    pub fn root(&self) -> Node {
        assert!(!self.nodes.is_empty(), "Merkle tree has no nodes");
        self.nodes[0]
    }

    /// Get number of leaves in the Merkle tree.
    pub fn num_leaves(&self) -> usize {
        1 << (self.depth() - 1)
    }

    /// Check if given index is index of the leaf.
    pub fn is_leaf_node_index(&self, index: usize) -> bool {
        self.num_leaves() - 1 <= index && index < self.nodes.len()
    }

    /// Convert index of the leaf to index of the node in the array.
    pub fn leaf_index_to_index(&self, leaf_index: usize) -> Result<usize> {
        let leaves_count = self.num_leaves();
        if leaf_index >= leaves_count {
            Err(anyhow!(
                "Leaf index must be less than {} ({} was given)",
                leaves_count,
                leaf_index
            ))
        } else {
            let index = self.num_leaves() + leaf_index - 1;
            assert!(index < self.nodes.len());
            Ok(index)
        }
    }

    /// Set value of leaf at given index.
    ///
    /// It updates the hashes of all nodes on the path to the root. Notice the corner case: if there
    /// is just one node in the tree, its hash is updated.
    pub fn set(&mut self, leaf_index: usize, value: Node) -> Result<Node> {
        let mut index = self.leaf_index_to_index(leaf_index)?;
        let n = self.nodes.len();
        assert!(
            index < n,
            "Leaf index {} out of bounds (max allowed leaf index is {})",
            index,
            n - 1
        );
        if self.nodes[index] == value {
            Ok(self.root())
        } else {
            self.nodes[index] = value;
            while index > 0 {
                index = ((index as isize - 1) / 2) as usize;
                self.update_node_hash(index)?;
            }
            self.update_node_hash(0)
        }
    }

    /// Get proof for leaf at given index.
    pub fn proof(&self, leaf_index: usize) -> Result<Vec<(Direction, Node)>> {
        let mut index = self.leaf_index_to_index(leaf_index)?;
        let mut proof = Vec::new();
        while index != 0 {
            let direction = if index % 2 == 0 {
                Direction::Right
            } else {
                Direction::Left
            };
            let sibling_index = if direction == Direction::Right {
                index - 1
            } else {
                index + 1
            };
            assert!(sibling_index < self.nodes.len());
            proof.push((direction, self.nodes[sibling_index]));
            index = Self::index_of_parent(index);
        }
        Ok(proof)
    }

    /// Verify proof for leaf at given index.
    pub fn verify(&self, proof: &[(Direction, Node)], leaf: Node) -> Result<Node> {
        let mut hash = leaf;

        for &(direction, sibling) in proof {
            let slices = if direction == Direction::Right {
                [sibling.as_slice(), hash.as_slice()].concat()
            } else {
                [hash.as_slice(), sibling.as_slice()].concat()
            };
            hash = Sha3_256::digest(&slices);
        }

        Ok(hash)
    }

    fn update_node_hash(&mut self, index: usize) -> Result<Node> {
        if index >= self.nodes.len() {
            Err(anyhow!(
                "Index {} out of bounds (max allowed index is {})",
                index,
                self.nodes.len() - 1
            ))
        } else if self.is_leaf_node_index(index) {
            Ok(self.nodes[index]) // nothing to do for leaf nodes
        } else {
            assert!(2 * index + 2 < self.nodes.len());
            let left_child = self.nodes[index * 2 + 1];
            let right_child = self.nodes[index * 2 + 2];
            let mut hasher = Sha3_256::new();
            hasher.update(left_child);
            hasher.update(right_child);
            self.nodes[index] = hasher.finalize();
            Ok(self.nodes[index])
        }
    }
}

#[cfg(test)]
mod test {
    use core::ops::Mul;

    use super::*;

    #[test]
    fn test_create_big_tree() {
        let depth = 20;
        let tree = MerkleTree::new(depth, [0u8; 32].into());
        assert!(tree.is_ok());
    }

    #[test]
    fn test_depth() {
        for depth in 1..10 {
            let tree = MerkleTree::new(depth, [0u8; 32].into());
            assert_eq!(tree.unwrap().depth(), depth);
        }
    }

    #[test]
    fn test_depth_and_offset_to_index() {
        let cases = [
            (0, 0, 0),
            (1, 0, 1),
            (1, 1, 2),
            (2, 0, 3),
            (2, 1, 4),
            (2, 2, 5),
            (2, 3, 6),
            (3, 0, 7),
            (3, 1, 8),
            (3, 2, 9),
            (3, 3, 10),
            (3, 4, 11),
            (3, 5, 12),
            (3, 6, 13),
            (3, 7, 14),
        ];

        for &(depth, offset, expected) in &cases {
            let index = MerkleTree::depth_and_offset_to_index(depth, offset);
            assert_eq!(index.unwrap(), expected);
        }
    }

    #[test]
    fn test_depth_and_offset_to_index_error() {
        let cases = [(0, 1), (1, 2), (1, 3), (2, 5), (5, 10000)];

        for &(depth, offset) in &cases {
            let result = MerkleTree::depth_and_offset_to_index(depth, offset);
            assert!(result.is_err());
        }
    }

    #[test]
    fn test_index_to_depth_and_offset() {
        let cases = vec![
            (0, (0, 0)),
            (1, (1, 0)),
            (2, (1, 1)),
            (3, (2, 0)),
            (4, (2, 1)),
            (5, (2, 2)),
            (6, (2, 3)),
            (7, (3, 0)),
            (15, (4, 0)),
            (22, (4, 7)),
            (31, (5, 0)),
        ];

        for (index, (expected_depth, expected_offset)) in cases {
            let (depth, offset) = MerkleTree::index_to_depth_and_offset(index);
            assert_eq!(depth, expected_depth);
            assert_eq!(offset, expected_offset);
        }
    }

    #[test]
    fn test_index_of_parent() {
        let cases = vec![
            (0, 0),
            (1, 0),
            (2, 0),
            (3, 1),
            (4, 1),
            (5, 2),
            (6, 2),
            (7, 3),
            (22, 10),
            (30, 14),
            (31, 15),
        ];

        for (index, expected_parent_index) in cases {
            let parent_index = MerkleTree::index_of_parent(index);
            assert_eq!(parent_index, expected_parent_index);
        }
    }

    #[test]
    fn test_leftmost_index() {
        let depth = 5;
        let tree = MerkleTree::new(depth, [0u8; 32].into()).unwrap();
        let cases = vec![
            (0, 15),
            (1, 15),
            (2, 23),
            (3, 15),
            (4, 19),
            (5, 23),
            (6, 27),
            (15, 15),
            (16, 16),
            (30, 30),
        ];

        for (index, expected_leftmost_index) in cases {
            let leftmost_index = tree.leftmost_index(index).unwrap();
            assert_eq!(leftmost_index, expected_leftmost_index);
        }
    }

    #[test]
    fn test_leftmost_index_error() {
        let depth = 5;
        let tree = MerkleTree::new(depth, [0u8; 32].into()).unwrap();
        let cases = vec![31, 32, 10000, 99_999_999];

        for index in cases {
            let result = tree.leftmost_index(index);
            assert!(result.is_err());
        }
    }

    #[test]
    fn test_root() {
        let depth = 2;
        let initial_leaf = hex!("deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
        let tree = MerkleTree::new(depth, initial_leaf.into()).unwrap();
        let val_to_hash = [initial_leaf.as_slice(), initial_leaf.as_slice()].concat();
        let hash = Sha3_256::digest(val_to_hash);
        assert_eq!(tree.root(), hash);
        assert_ne!(tree.root(), initial_leaf.into());
    }

    #[test]
    fn test_root_with_one_node_tree() {
        let depth = 1;
        let initial_leaf = hex!("deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
        let tree = MerkleTree::new(depth, initial_leaf.into()).unwrap();
        assert_eq!(tree.root(), initial_leaf.into());
    }

    #[test]
    fn test_num_leaves() {
        let cases = vec![(1, 1), (2, 2), (3, 4), (4, 8), (5, 16), (6, 32)];

        for (depth, expected_num_leaves) in cases {
            let tree = MerkleTree::new(depth, [0u8; 32].into()).unwrap();
            let num_leaves = tree.num_leaves();
            assert_eq!(num_leaves, expected_num_leaves);
        }
    }

    #[test]
    fn test_is_leaf_node_index() {
        let depth = 5;
        let tree = MerkleTree::new(depth, [0u8; 32].into()).unwrap();

        for index in 0..1_000_000 {
            if (15..31).contains(&index) {
                assert!(tree.is_leaf_node_index(index));
            } else {
                assert!(!tree.is_leaf_node_index(index));
            }
        }
    }

    #[test]
    fn test_leaf_index_to_index() {
        let depth = 5;
        let tree = MerkleTree::new(depth, [0u8; 32].into()).unwrap();
        let mut expected_node_index = 15;

        for leaf_index in 0..16 {
            let node_index = tree.leaf_index_to_index(leaf_index).unwrap();
            assert_eq!(node_index, expected_node_index);
            expected_node_index += 1;
        }
    }

    #[test]
    fn test_leaf_index_to_index_out_of_bounds() {
        let depth = 5;
        let tree = MerkleTree::new(depth, [0u8; 32].into()).unwrap();

        for leaf_index in 16..1000 {
            let node_index = tree.leaf_index_to_index(leaf_index);
            assert!(node_index.is_err());
        }
    }

    #[test]
    fn test_set() {
        let depth = 6;
        let initial_leaf = hex!("0000000000000000000000000000000000000000000000000000000000000000");
        let mut tree = MerkleTree::new(depth, initial_leaf.into()).unwrap();
        let leaf_index_to_update = 31;
        let new_val = hex!("beefbeefbeefbeefbeefbeefbeefbeefbeefbeefbeefbeefbeefbeefbeefbeef");
        let res = tree.set(leaf_index_to_update, new_val.into());
        assert!(res.is_ok());
        let val_to_hash = [initial_leaf.as_slice(), new_val.as_slice()].concat();
        let index_to_update = tree.leaf_index_to_index(leaf_index_to_update).unwrap();
        let parent_index = MerkleTree::index_of_parent(index_to_update);
        assert_eq!(tree.nodes[parent_index], Sha3_256::digest(val_to_hash));
    }

    #[test]
    fn test_proof() {
        let depth = 5;
        let initial_leaf = hex!("0000000000000000000000000000000000000000000000000000000000000000");
        let mut tree = MerkleTree::new(depth, initial_leaf.into()).unwrap();

        for i in 0..tree.num_leaves() {
            let num = BigUint::from_str_radix(
                "1111111111111111111111111111111111111111111111111111111111111111",
                16,
            )
            .unwrap();
            let mut new_val = num.mul(i).to_bytes_be();
            new_val.resize(32, 0); // conversion to GenericArray is tricky :(
            let new_val_arr = GenericArray::from_slice(new_val.as_slice());
            let res = tree.set(i, *new_val_arr);
            assert!(res.is_ok());
            assert_eq!(tree.root(), res.unwrap());
        }

        assert_eq!(
            tree.root(),
            hex!("57054e43fa56333fd51343b09460d48b9204999c376624f52480c5593b91eff4").into()
        );
        assert_eq!(
            tree.proof(3).unwrap(),
            [
                (
                    Direction::Right,
                    hex!("2222222222222222222222222222222222222222222222222222222222222222").into()
                ),
                (
                    Direction::Right,
                    hex!("35e794f1b42c224a8e390ce37e141a8d74aa53e151c1d1b9a03f88c65adb9e10").into()
                ),
                (
                    Direction::Left,
                    hex!("26fca7737f48fa702664c8b468e34c858e62f51762386bd0bddaa7050e0dd7c0").into()
                ),
                (
                    Direction::Left,
                    hex!("e7e11a86a0c1d8d8624b1629cb58e39bb4d0364cb8cb33c4029662ab30336858").into()
                ),
            ]
        );
    }

    #[test]
    fn test_set_out_of_bounds() {
        let depth = 5;
        let mut tree = MerkleTree::new(depth, [0u8; 32].into()).unwrap();
        let res = tree.set(16, [1u8; 32].into());
        assert!(res.is_err());
    }

    #[test]
    fn test_verify() {
        let depth = 5;
        let initial_leaf = hex!("0000000000000000000000000000000000000000000000000000000000000000");
        let mut tree = MerkleTree::new(depth, initial_leaf.into()).unwrap();

        for i in 0..tree.num_leaves() {
            let num = BigUint::from_str_radix(
                "1111111111111111111111111111111111111111111111111111111111111111",
                16,
            )
            .unwrap();
            let mut new_val = num.mul(i).to_bytes_be();
            new_val.resize(32, 0); // conversion to GenericArray is tricky :(
            let new_val_arr = GenericArray::from_slice(new_val.as_slice());
            let res = tree.set(i, *new_val_arr);
        }

        let leaf_5 = BigUint::from_str_radix(
            "1111111111111111111111111111111111111111111111111111111111111111",
            16,
        )
        .unwrap()
        .mul(5u32);
        let root = tree.root();
        let proof = tree.proof(5).unwrap();
        assert_eq!(
            tree.verify(
                &proof,
                *GenericArray::from_slice(leaf_5.to_bytes_be().as_slice())
            )
            .unwrap(),
            root
        );
    }
}
