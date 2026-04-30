//! A minimal univariate STARK framework.

#![no_std]

extern crate alloc;

mod check_constraints;
mod clean_air;
mod clean_ast;
mod config;
mod key;
mod lookup;
mod permutation;
mod prover;
mod verifier;

pub use check_constraints::*;
pub use clean_air::*;
pub use clean_ast::*;
pub use config::*;
pub use key::*;
pub use lookup::*;
pub use permutation::*;
pub use prover::prove;
pub use verifier::verify;
