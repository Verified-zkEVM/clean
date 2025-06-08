//! A minimal univariate STARK framework.

#![no_std]

extern crate alloc;

mod check_constraints;
mod clean_air;
mod clean_ast;
mod config;
mod folder;
mod key;
mod lookup;
mod permutation;
mod proof;
mod prover;
mod verifier;

pub use check_constraints::*;
pub use clean_air::*;
pub use clean_ast::*;
pub use config::*;
pub use folder::{ProverConstraintFolder, VerifierConstraintFolder};
pub use key::*;
pub use lookup::*;
pub use permutation::*;
pub use proof::*;
pub use prover::prove;
pub use verifier::verify;
