use alloc::vec::Vec;
use p3_air::lookup::{Kind, Lookup, LookupData, LookupEvaluator};
use p3_air::{
    Air, AirBuilder, AirBuilderWithPublicValues, BaseAir,
};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::Field;
use p3_lookup::logup::LogUpGadget;
use p3_lookup::lookup_traits::lookup_data_to_expr;
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_uni_stark::{SymbolicAirBuilder, SymbolicExpression};
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

/// Evaluate all constraints (AIR + lookup) symbolically, returning both
/// base and extension constraint expressions.
///
/// Mirrors the upstream batch-stark `get_symbolic_constraints` pattern:
/// builds a `SymbolicAirBuilder` with proper permutation width and challenge
/// count, then calls `eval_with_lookups` to collect ALL constraints.
fn get_all_constraints_with_lookups<F: Field>(
    air: &CleanAirInstance<F>,
    lookups: &[Lookup<F>],
    preprocessed_width: usize,
    public_inputs: usize,
) -> (Vec<SymbolicExpression<F>>, Vec<SymbolicExpression<F>>) {
    let gadget = LogUpGadget::new();
    let num_lookups = lookups.len();
    let num_aux_cols = num_lookups * gadget.num_aux_cols();
    let num_challenges = num_lookups * gadget.num_challenges();

    let mut builder = SymbolicAirBuilder::new(
        preprocessed_width,
        air.width(),
        public_inputs,
        num_aux_cols,
        num_challenges,
    );

    // Build dummy symbolic LookupData for global lookups
    let lookup_data: Vec<LookupData<F>> = lookups
        .iter()
        .filter_map(|l| {
            if let Kind::Global(name) = &l.kind {
                Some(LookupData {
                    name: name.clone(),
                    aux_idx: l.columns[0],
                    expected_cumulated: F::ZERO,
                })
            } else {
                None
            }
        })
        .collect();
    let symbolic_lookup_data = lookup_data_to_expr(&lookup_data);

    // Evaluate AIR + lookup constraints symbolically
    air.eval_with_lookups(&mut builder, lookups, &symbolic_lookup_data, &gadget);

    (builder.base_constraints(), builder.extension_constraints())
}

impl<F: Field> VerifyingKey<F> for AirInfo<F> {
    fn lookups(&self) -> &[Lookup<F>] {
        &self.lookups
    }

    fn preprocessed(&self) -> Option<RowMajorMatrix<F>> {
        self.preprocessed.clone()
    }

    fn count_constraints(&self, public_inputs: usize) -> usize {
        let preprocessed_width = self.preprocessed.as_ref().map_or(0, |p| p.width());
        let (base, ext) = get_all_constraints_with_lookups(
            &self.air,
            &self.lookups,
            preprocessed_width,
            public_inputs,
        );
        base.len() + ext.len()
    }

    fn log_quotient_degree(&self, public_inputs: usize) -> usize {
        let preprocessed_width = self.preprocessed.as_ref().map_or(0, |p| p.width());
        let (base, ext) = get_all_constraints_with_lookups(
            &self.air,
            &self.lookups,
            preprocessed_width,
            public_inputs,
        );
        let max_degree = base
            .iter()
            .chain(ext.iter())
            .map(|c| c.degree_multiple())
            .max()
            .unwrap_or(0)
            .max(2); // pad to at least degree 2

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
