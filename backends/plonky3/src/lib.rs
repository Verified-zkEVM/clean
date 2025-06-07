//! A minimal univariate STARK framework.

#![no_std]

extern crate alloc;

mod config;
mod folder;
mod lookup;
mod proof;
mod prover;
mod verifier;
mod check_constraints;
mod clean_air;
mod permutation;

pub use check_constraints::*;
pub use config::*;
pub use folder::{ProverConstraintFolder, VerifierConstraintFolder};
pub use proof::*;
pub use prover::prove;
pub use lookup::*;
pub use verifier::verify;
pub use clean_air::*;
pub use permutation::*;
