# Batching Efficient RAM From Updatable Lookup Arguments
This repository contains implementation of lookup arguments from updatable tables, detailed in the paper 
"Batching Efficient RAM Using Updatable Lookup Arguments" [paper](https://eprint.iacr.org/2024/840.pdf) appearing 
in ACM CCS 2024. 

WARNING:  This project contains a proof of concept implementation of the above paper and has not received any formal audit.  It should not be used production.
n this project.

The repository is a fork of the original implementation of Caulk [caulk](https://eprint.iacr.org/2022/621) 
sub-vector lookup argument available at [caulk-crypto](https://github.com/caulk-crypto/caulk). We re-use 
many components such proof transcripts and algebraic algorithms from the Caulk implementation. 

The remainder of the document gives a tutorial introduction to the code, and how to run and reproduce some 
of the benchmarks reported in the paper. 

## Code Overview
The changes corresponding to the updatable lookup tables appear in the `updatable-ram` branch of the repo. 

- Several new algebraic algorithms for polynomial interpolation and evaluation are added to `src/single/dft.rs`
on top of the existing algorithms from the Caulk repository.
- Implementation of CQ lookup protocol based on the paper [CQ](https://eprint.iacr.org/2022/1763), with additional option of computing CQ lookup argument using 
pre-processed parameters for an "approximate" table. This code appears in the file `src/ramlookup/cq.rs`. 
- A fast $O(\delta\log^2 \delta)$ algorithm for computing scalar coefficients for computing the additive encoded quotient on 
top of the base CQ cached quotient. This appears in `src/ramlookup/fastupdate.rs`.
- An implementation of polynomial protocol for memory consistency appears in `src/ramlookup/mod.rs`. Currently, 
the protocols for checking well formation of time ordered transcript and address ordered transcript are implemented. 
We hope to implement remaining protocols in the future, but they are not critical to overall benchmarks, as these are 
over much smaller tables.

## Running Benchmarks for CQ Argument from Updatable Tables
This scenario considers two tables, which we call `base_table`, for which we have pre-computed cached quotients (as in the CQ protocol), and `current_table`
which differs from the `base_table` at some $K$ locations. Moreover, we consider a sub-vector `f_vec` of `current_table` of size $m$. The example here 
constructs an argument for showing `f_vec` is a sub-vector of `current_table`. To run this example one executes the following command from the repository root directory (one containing `Cargo.toml`).

```shell
~/.cargo/bin/cargo test --color=always --release --package caulk --lib ramlookup::cq::tests::test_run_full_protocol -- --exact --nocapture
```
The above command assumes cargo is installed in the user's home directory. It should be changed appropriately to point to the rust installation. The above command runs the test function 
`test_run_full_protocol` in the file `src/ramlookup/cq.rs`. The test can be run for different parameters by changing the following constants in the test module in the same file.

```rust 
mod tests {
    use std::time::Instant;
    use ark_bls12_381::Bls12_381;
    use super::*;

    const h_domain_size: usize = 20;
    const m_domain_size: usize = 10;
    const k_domain_size: usize = 18;
    // ...
}
```
Here `N=1 << h_domain_size` gives the size of the tables, `m=1 << m_domain_size` gives the size of the sub-vector while `K=1 << k_domain_size` gives the maximum hamming distance between the base table 
and the current table.
