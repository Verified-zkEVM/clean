//! Plonky3 backend for channel-based Clean AIR ensembles.

#![no_std]

extern crate alloc;

mod ensemble_macro;
mod ensemble_prover;
mod generated_air;
pub mod witness_generation;

pub use ensemble_prover::{
    prove_ensemble, verify_ensemble, EnsembleProvingError, EnsembleVerificationError,
    PcsProverError,
};
pub use generated_air::*;
pub use p3_batch_stark::{BatchProof, PcsError, StarkGenericConfig, Val};
pub use p3_uni_stark::StarkConfig;

/// Items used by the code that [`ensemble`] expands to.
#[doc(hidden)]
pub mod __private {
    pub use alloc::string::String;
    pub use alloc::vec::Vec;
    pub use alloc::{format, vec};
    pub use p3_field::PrimeCharacteristicRing;
}
