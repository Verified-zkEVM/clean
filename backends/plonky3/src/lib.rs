//! A minimal univariate STARK framework.

#![no_std]

extern crate alloc;

mod config;
mod ensemble_prover;
mod generated_air;
pub mod witness_generation;

pub use config::*;
pub use ensemble_prover::{prove_ensemble, verify_ensemble, EnsembleVerificationError};
pub use generated_air::*;
