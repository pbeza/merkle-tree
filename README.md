# Simplified Merkle Tree

## Description

This application is a simplified Rust implementation of [Merkle Tree](https://en.wikipedia.org/wiki/Merkle_tree). Please refer to the unit tests to understand its capabilities.

## Features

- Creation of Merkle Trees from an initial leaf.
- Generation of proofs for a given leaf index.
- Verification of proofs.
- Updating a single leaf value and recomputing the affected nodes.
- Conversion of node indices to `(depth, offset)` format and vice versa.
- Finding the index of the left-most child and parent.
