use alloc::vec::Vec;
use p3_air::{
    Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PairBuilder, PairCol, VirtualPairCol,
};
use p3_field::Field;
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use p3_uni_stark::{Entry, SymbolicExpression, SymbolicVariable};

#[derive(Debug, Clone)]
pub enum LookupType {
    ByteRange,
}

#[derive(Debug, Clone)]
pub struct Lookup<E> {
    pub kind: LookupType,
    // todo: support compressing multiple column values
    pub value: E,
    pub multiplicity: E,
}

impl<E> Lookup<E> {
    pub fn new(kind: LookupType, value: E, multiplicity: E) -> Self {
        Self {
            kind,
            value,
            multiplicity,
        }
    }
}

pub trait MessageBuilder<L> {
    fn send(&mut self, _l: L) {}
    fn receive(&mut self, _l: L) {}
}

pub trait BaseMessageBuilder: AirBuilder + MessageBuilder<Lookup<Self::Expr>> {}

pub struct LookupBuilder<F>
where
    F: Field,
{
    preprocessed: RowMajorMatrix<SymbolicVariable<F>>,
    main: RowMajorMatrix<SymbolicVariable<F>>,
    sends: Vec<Lookup<VirtualPairCol<F>>>,
    receives: Vec<Lookup<VirtualPairCol<F>>>,
    public_values: Vec<F>,
}

impl<F: Field> LookupBuilder<F> {
    pub fn new(preprocessed_width: usize, main_width: usize) -> Self {
        let preprocessed_width = preprocessed_width.max(1);
        let prep_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..preprocessed_width).map(move |column| {
                    SymbolicVariable::new(Entry::Preprocessed { offset }, column)
                })
            })
            .collect();

        let main_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..main_width)
                    .map(move |column| SymbolicVariable::new(Entry::Main { offset }, column))
            })
            .collect();

        Self {
            preprocessed: RowMajorMatrix::new(prep_values, preprocessed_width),
            main: RowMajorMatrix::new(main_values, main_width),
            sends: Vec::new(),
            receives: Vec::new(),
            public_values: Vec::from([F::ZERO, F::ONE, F::ONE]),
        }
    }

    pub fn messages(
        &self,
    ) -> (
        Vec<Lookup<VirtualPairCol<F>>>,
        Vec<Lookup<VirtualPairCol<F>>>,
    ) {
        (self.sends.clone(), self.receives.clone())
    }
}

impl<F: Field> AirBuilder for LookupBuilder<F> {
    type F = F;
    type Expr = SymbolicExpression<F>;
    type Var = SymbolicVariable<F>;
    type M = RowMajorMatrix<Self::Var>;

    fn main(&self) -> Self::M {
        self.main.clone()
    }

    fn is_first_row(&self) -> Self::Expr {
        SymbolicExpression::IsFirstRow
    }

    fn is_last_row(&self) -> Self::Expr {
        SymbolicExpression::IsLastRow
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            SymbolicExpression::IsTransition
        } else {
            panic!("uni-stark only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, _x: I) {}
}

impl<F: Field> PairBuilder for LookupBuilder<F> {
    fn preprocessed(&self) -> Self::M {
        self.preprocessed.clone()
    }
}

impl<F: Field> AirBuilderWithPublicValues for LookupBuilder<F> {
    type PublicVar = F;

    fn public_values(&self) -> &[Self::PublicVar] {
        &self.public_values
    }
}

impl<F: Field> MessageBuilder<Lookup<SymbolicExpression<F>>> for LookupBuilder<F> {
    fn send(&mut self, l: Lookup<SymbolicExpression<F>>) {
        let l = Lookup::new(
            l.kind,
            symbolic_to_virtual_pair(&l.value),
            symbolic_to_virtual_pair(&l.multiplicity),
        );
        self.sends.push(l);
    }

    fn receive(&mut self, l: Lookup<SymbolicExpression<F>>) {
        let l = Lookup::new(
            l.kind,
            symbolic_to_virtual_pair(&l.value),
            symbolic_to_virtual_pair(&l.multiplicity),
        );
        self.receives.push(l);
    }
}

impl<F: Field> BaseMessageBuilder for LookupBuilder<F> {}

fn symbolic_to_virtual_pair<F: Field>(expression: &SymbolicExpression<F>) -> VirtualPairCol<F> {
    if expression.degree_multiple() > 1 {
        panic!("degree multiple is too high");
    }

    let (column_weights, constant) = eval_symbolic_to_virtual_pair(expression);

    let column_weights = column_weights.into_iter().collect();

    VirtualPairCol::new(column_weights, constant)
}

fn eval_symbolic_to_virtual_pair<F: Field>(
    expression: &SymbolicExpression<F>,
) -> (Vec<(PairCol, F)>, F) {
    match expression {
        SymbolicExpression::Constant(c) => (Vec::new(), *c),
        SymbolicExpression::Variable(v) => match v.entry {
            Entry::Preprocessed { offset: 0 } => (
                Vec::from([(PairCol::Preprocessed(v.index), F::ONE)]),
                F::ZERO,
            ),
            Entry::Main { offset: 0 } => (Vec::from([(PairCol::Main(v.index), F::ONE)]), F::ZERO),
            _ => panic!(
                "not an affine expression in current row elements {:?}",
                v.entry
            ),
        },
        SymbolicExpression::Add { x, y, .. } => {
            let (v_l, c_l) = eval_symbolic_to_virtual_pair(x);
            let (v_r, c_r) = eval_symbolic_to_virtual_pair(y);
            ([v_l, v_r].concat(), c_l + c_r)
        }
        SymbolicExpression::Sub { x, y, .. } => {
            let (v_l, c_l) = eval_symbolic_to_virtual_pair(x);
            let (v_r, c_r) = eval_symbolic_to_virtual_pair(y);
            let neg_v_r = v_r.iter().map(|(c, w)| (*c, -*w)).collect();
            ([v_l, neg_v_r].concat(), c_l - c_r)
        }
        SymbolicExpression::Neg { x, .. } => {
            let (v, c) = eval_symbolic_to_virtual_pair(x);
            (v.iter().map(|(c, w)| (*c, -*w)).collect(), -c)
        }
        SymbolicExpression::Mul { x, y, .. } => {
            let (v_l, c_l) = eval_symbolic_to_virtual_pair(x);
            let (v_r, c_r) = eval_symbolic_to_virtual_pair(y);

            let mut v = Vec::new();
            v.extend(v_l.iter().map(|(c, w)| (*c, *w * c_r)));
            v.extend(v_r.iter().map(|(c, w)| (*c, *w * c_l)));

            if !v_l.is_empty() && !v_r.is_empty() {
                panic!("Not an affine expression")
            }

            (v, c_l * c_r)
        }
        SymbolicExpression::IsFirstRow => {
            panic!("not an affine expression in current row elements for first row")
        }
        SymbolicExpression::IsLastRow => {
            panic!("not an affine expression in current row elements for last row")
        }
        SymbolicExpression::IsTransition => {
            panic!("not an affine expression in current row elements for transition row")
        }
    }
}

#[derive(Clone)]
pub struct ByteRangeAir<F> {
    pub preprocessed: RowMajorMatrix<F>,
}

impl<F: Field> ByteRangeAir<F> {
    pub fn new() -> Self {
        let preprocessed = RowMajorMatrix::new((0..256).map(|i| F::from_u8(i as u8)).collect(), 1);
        Self { preprocessed }
    }
}

impl<F: Field> BaseAir<F> for ByteRangeAir<F> {
    /// One column for multiplicity
    fn width(&self) -> usize {
        1
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(self.preprocessed.clone())
    }
}

impl<AB: PairBuilder + BaseMessageBuilder> Air<AB> for ByteRangeAir<AB::F>
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        // generate receive lookups
        let main = builder.main();
        let preprocessed = builder.preprocessed();

        let local_mul = main.get(0, 0).unwrap().into();
        let local_preprocessed_val = preprocessed.get(0, 0).unwrap().into();

        let receive = Lookup::new(LookupType::ByteRange, local_preprocessed_val, local_mul);
        builder.receive(receive);
    }
}

// Implementation for SymbolicAirBuilder from p3_uni_stark
impl<F> MessageBuilder<Lookup<p3_uni_stark::SymbolicExpression<F>>>
    for p3_uni_stark::SymbolicAirBuilder<F>
where
    F: Field,
{
    // Default implementations are provided by the trait
}

impl<F> BaseMessageBuilder for p3_uni_stark::SymbolicAirBuilder<F> where F: Field {}
