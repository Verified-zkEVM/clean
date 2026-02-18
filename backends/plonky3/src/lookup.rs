use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_field::Field;
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use p3_uni_stark::{Entry, SymbolicExpression, SymbolicVariable};

#[derive(Debug, Clone)]
pub struct Lookup<E> {
    pub table_name: String,
    pub values: Vec<E>,
    pub multiplicity: E,
}

impl<E> Lookup<E> {
    pub fn new(table_name: String, values: Vec<E>, multiplicity: E) -> Self {
        Self {
            table_name,
            values,
            multiplicity,
        }
    }
}

/// Expression tree for lookup values that supports both current-row and next-row references.
/// Unlike `VirtualPairCol` which only supports affine combinations of current-row columns,
/// `LookupExpr` can represent arbitrary expressions over local, next, and preprocessed columns.
#[derive(Debug, Clone)]
pub enum LookupExpr<F> {
    MainLocal(usize),
    MainNext(usize),
    Preprocessed(usize),
    Const(F),
    Add(Box<LookupExpr<F>>, Box<LookupExpr<F>>),
    Sub(Box<LookupExpr<F>>, Box<LookupExpr<F>>),
    Mul(Box<LookupExpr<F>>, Box<LookupExpr<F>>),
    Neg(Box<LookupExpr<F>>),
}

impl<F: Field> LookupExpr<F> {
    /// Evaluate the expression given concrete row values (for trace generation).
    pub fn eval(&self, preprocessed: &[F], main_local: &[F], main_next: &[F]) -> F {
        match self {
            LookupExpr::MainLocal(col) => main_local[*col],
            LookupExpr::MainNext(col) => main_next[*col],
            LookupExpr::Preprocessed(col) => preprocessed[*col],
            LookupExpr::Const(c) => *c,
            LookupExpr::Add(a, b) => {
                a.eval(preprocessed, main_local, main_next)
                    + b.eval(preprocessed, main_local, main_next)
            }
            LookupExpr::Sub(a, b) => {
                a.eval(preprocessed, main_local, main_next)
                    - b.eval(preprocessed, main_local, main_next)
            }
            LookupExpr::Mul(a, b) => {
                a.eval(preprocessed, main_local, main_next)
                    * b.eval(preprocessed, main_local, main_next)
            }
            LookupExpr::Neg(a) => -a.eval(preprocessed, main_local, main_next),
        }
    }

    /// Convert to an AirBuilder expression (for constraint evaluation).
    pub fn to_air_expr<AB: AirBuilder<F = F>>(
        &self,
        preprocessed: &[AB::Var],
        main_local: &[AB::Var],
        main_next: &[AB::Var],
    ) -> AB::Expr
    where
        AB::Var: Copy,
    {
        match self {
            LookupExpr::MainLocal(col) => main_local[*col].into(),
            LookupExpr::MainNext(col) => main_next[*col].into(),
            LookupExpr::Preprocessed(col) => preprocessed[*col].into(),
            LookupExpr::Const(c) => (*c).into(),
            LookupExpr::Add(a, b) => {
                a.to_air_expr::<AB>(preprocessed, main_local, main_next)
                    + b.to_air_expr::<AB>(preprocessed, main_local, main_next)
            }
            LookupExpr::Sub(a, b) => {
                a.to_air_expr::<AB>(preprocessed, main_local, main_next)
                    - b.to_air_expr::<AB>(preprocessed, main_local, main_next)
            }
            LookupExpr::Mul(a, b) => {
                a.to_air_expr::<AB>(preprocessed, main_local, main_next)
                    * b.to_air_expr::<AB>(preprocessed, main_local, main_next)
            }
            LookupExpr::Neg(a) => -a.to_air_expr::<AB>(preprocessed, main_local, main_next),
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
    sends: Vec<Lookup<LookupExpr<F>>>,
    receives: Vec<Lookup<LookupExpr<F>>>,
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
        Vec<Lookup<LookupExpr<F>>>,
        Vec<Lookup<LookupExpr<F>>>,
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

    fn preprocessed(&self) -> Option<Self::M> {
        Some(self.preprocessed.clone())
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
            l.table_name,
            l.values
                .iter()
                .map(|v| symbolic_to_lookup_expr(v))
                .collect(),
            symbolic_to_lookup_expr(&l.multiplicity),
        );
        self.sends.push(l);
    }

    fn receive(&mut self, l: Lookup<SymbolicExpression<F>>) {
        let l = Lookup::new(
            l.table_name,
            l.values
                .iter()
                .map(|v| symbolic_to_lookup_expr(v))
                .collect(),
            symbolic_to_lookup_expr(&l.multiplicity),
        );
        self.receives.push(l);
    }
}

impl<F: Field> BaseMessageBuilder for LookupBuilder<F> {}

/// Convert a `SymbolicExpression` to a `LookupExpr`.
/// Supports current-row, next-row, and preprocessed column references,
/// as well as arbitrary arithmetic expressions (not limited to affine).
fn symbolic_to_lookup_expr<F: Field>(expression: &SymbolicExpression<F>) -> LookupExpr<F> {
    match expression {
        SymbolicExpression::Constant(c) => LookupExpr::Const(*c),
        SymbolicExpression::Variable(v) => match v.entry {
            Entry::Preprocessed { offset: 0 } => LookupExpr::Preprocessed(v.index),
            Entry::Main { offset: 0 } => LookupExpr::MainLocal(v.index),
            Entry::Main { offset: 1 } => LookupExpr::MainNext(v.index),
            _ => panic!("Unsupported entry type {:?}", v.entry),
        },
        SymbolicExpression::Add { x, y, .. } => LookupExpr::Add(
            Box::new(symbolic_to_lookup_expr(x)),
            Box::new(symbolic_to_lookup_expr(y)),
        ),
        SymbolicExpression::Sub { x, y, .. } => LookupExpr::Sub(
            Box::new(symbolic_to_lookup_expr(x)),
            Box::new(symbolic_to_lookup_expr(y)),
        ),
        SymbolicExpression::Mul { x, y, .. } => LookupExpr::Mul(
            Box::new(symbolic_to_lookup_expr(x)),
            Box::new(symbolic_to_lookup_expr(y)),
        ),
        SymbolicExpression::Neg { x, .. } => {
            LookupExpr::Neg(Box::new(symbolic_to_lookup_expr(x)))
        }
        _ => panic!("Unsupported expression type in lookup conversion"),
    }
}

#[derive(Clone)]
pub struct PreprocessedTableAir<F> {
    pub name: String,
    pub preprocessed: RowMajorMatrix<F>,
}

impl<F: Field> PreprocessedTableAir<F> {
    pub fn new(name: String, preprocessed: RowMajorMatrix<F>) -> Self {
        Self { name, preprocessed }
    }

    pub fn table_name(&self) -> &str {
        &self.name
    }
}

/// Convenience constructor for a byte-range (0..255) lookup table.
pub fn byte_range_air<F: Field>() -> PreprocessedTableAir<F> {
    let preprocessed = RowMajorMatrix::new((0..256).map(|i| F::from_u8(i as u8)).collect(), 1);
    PreprocessedTableAir::new("Bytes".into(), preprocessed)
}

impl<F: Field> BaseAir<F> for PreprocessedTableAir<F> {
    /// One column for multiplicity
    fn width(&self) -> usize {
        1
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        Some(self.preprocessed.clone())
    }
}

impl<AB: AirBuilder + BaseMessageBuilder> Air<AB> for PreprocessedTableAir<AB::F>
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        // generate receive lookups
        let main = builder.main();
        let preprocessed = builder
            .preprocessed()
            .expect("PreprocessedTableAir requires preprocessed trace");

        let local_mul = main.get(0, 0).unwrap().into();

        // Multi-column: emit one value per preprocessed column
        let values: Vec<AB::Expr> = (0..self.preprocessed.width())
            .map(|col| preprocessed.get(0, col).unwrap().into())
            .collect();

        let receive = Lookup::new(self.name.clone(), values, local_mul);
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
