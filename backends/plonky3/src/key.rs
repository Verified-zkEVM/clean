use alloc::vec::Vec;
use p3_air::lookup::Lookup;
use p3_air::{
    Air, AirBuilder, AirBuilderWithPublicValues, BaseAir,
};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::Field;
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_uni_stark::{get_symbolic_constraints, SymbolicExpression};
use p3_util::log2_ceil_usize;

// Bring vec! macro into scope
extern crate alloc;
use alloc::vec;

use crate::clean_air::CleanAirInstance;
use crate::{StarkGenericConfig, Val};

type Com<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Commitment;

type PcsData<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::ProverData;

pub trait VerifyingKey<F: Field> {
    fn lookups(&self) -> &[Lookup<F>];
    /// Returns the width of the main trace
    fn width(&self) -> usize;
    fn preprocessed(&self) -> Option<RowMajorMatrix<F>> {
        None
    }
    fn constraints(&self, public_inputs: usize) -> Vec<SymbolicExpression<F>>;
    fn count_constraints(&self, public_inputs: usize) -> usize;
    fn log_quotient_degree(&self, public_inputs: usize) -> usize;
}

pub struct VK<SC: StarkGenericConfig> {
    air_infos: Vec<AirInfo<Val<SC>>>,
    pre_com: Com<SC>,
    pre_data: PcsData<SC>,
}

impl<SC: StarkGenericConfig> VK<SC> {
    /// Create a new VK with preprocessed trace commitment from a list of air instances
    pub fn new(air_infos: Vec<AirInfo<Val<SC>>>, traces_heights: Vec<usize>, config: &SC) -> Self {
        let pcs = config.pcs();
        // Collect all preprocessed traces for batch commitment
        let mut pre_and_domains = Vec::new();
        for (i, air_info) in air_infos.iter().enumerate() {
            if let Some(preprocessed_trace) = &air_info.preprocessed {
                let degree = preprocessed_trace.height();
                let domain = pcs.natural_domain_for_degree(degree);

                pre_and_domains.push((domain, preprocessed_trace.clone()));
            } else {
                // todo: remove the need for default preprocessed trace if no preprocessed trace is available
                // If no preprocessed trace, use a default matrix
                let domain = pcs.natural_domain_for_degree(traces_heights[i]);
                let default_matrix =
                    RowMajorMatrix::new(vec![Val::<SC>::default(); domain.size()], 1);
                pre_and_domains.push((domain, default_matrix));
            }
        }

        // Create batch commitment for all preprocessed traces
        let (pre_com, pre_data) = pcs.commit(pre_and_domains);

        Self {
            air_infos,
            pre_com,
            pre_data,
        }
    }

    /// Get the preprocessed trace commitment
    pub fn preprocessed_commitment(&self) -> &Com<SC> {
        &self.pre_com
    }

    /// Get the preprocessed trace data
    pub fn preprocessed_data(&self) -> &PcsData<SC> {
        &self.pre_data
    }

    /// Get access to all AirInfo instances
    pub fn air_infos(&self) -> &Vec<AirInfo<Val<SC>>> {
        &self.air_infos
    }
}

#[derive(Clone)]
pub struct AirInfo<F: Field> {
    pub air: CleanAirInstance<F>,
    pub lookups: Vec<Lookup<F>>,
    pub preprocessed: Option<RowMajorMatrix<F>>,
}

impl<F: Field> AirInfo<F> {
    /// Create a new AirInfo from air instance, building lookups automatically
    pub fn new(mut air: CleanAirInstance<F>) -> Self {
        // Build lookups using the air's build_lookups method
        let lookups = air.build_lookups();
        let preprocessed = air.preprocessed_trace();

        Self {
            air,
            lookups,
            preprocessed,
        }
    }
}

impl<F: Field> VerifyingKey<F> for AirInfo<F> {
    fn lookups(&self) -> &[Lookup<F>] {
        &self.lookups
    }

    fn preprocessed(&self) -> Option<RowMajorMatrix<F>> {
        self.preprocessed.clone()
    }

    fn constraints(&self, public_inputs: usize) -> Vec<SymbolicExpression<F>> {
        let preprocessed_width = if let Some(pre) = &self.preprocessed {
            pre.width()
        } else {
            0
        };

        get_symbolic_constraints(&self.air, preprocessed_width, public_inputs)
    }

    fn count_constraints(&self, public_inputs: usize) -> usize {
        let constraints = self.constraints(public_inputs);

        if !self.lookups.is_empty() {
            // For each lookup: 1 first-row + 1 transition + 1 last-row constraint = 3
            self.lookups.len() * 3 + constraints.len()
        } else {
            constraints.len()
        }
    }

    fn log_quotient_degree(&self, public_inputs: usize) -> usize {
        let constraints = self.constraints(public_inputs);
        let max_degree = constraints
            .iter()
            .map(|c| c.degree_multiple())
            .max()
            .unwrap_or(0);

        let max_degree = if !self.lookups.is_empty() {
            // LogUpGadget constraints have degree 3 (for global lookups with selector):
            // when_last_row constraint: is_last_row * (expected_cumulated - s) * denominator - numerator
            // The denominator is degree 1 (alpha - value), selector is degree 1, so total is 3.
            max_degree.max(3)
        } else {
            max_degree
        };

        // division by vanishing polynomial results in degree - 1
        log2_ceil_usize(max_degree - 1)
    }

    fn width(&self) -> usize {
        self.air.width()
    }
}

impl<F: Field> BaseAir<F> for AirInfo<F> {
    fn width(&self) -> usize {
        self.air.width()
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        self.air.preprocessed_trace()
    }
}

impl<AB> Air<AB> for AirInfo<AB::F>
where
    AB: AirBuilder + AirBuilderWithPublicValues,
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        self.air.eval(builder);
    }
}
