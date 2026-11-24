//! A circuit exported by Lean (`MidnightExport`) as a halo2 `Circuit`, shared by the key
//! comparison (`main.rs`) and the prover (`examples/prove.rs`).
use std::{cell::Cell as Flag, fs, io::BufReader, marker::PhantomData, path::Path, sync::Arc};
use ff::PrimeField;
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    circuit::{Cell, Layouter, Value},
    plonk::{Advice, Any, Circuit, Column, ConstraintSystem, Constraints, Error, Expression, Fixed, FloorPlanner,
        Instance, Selector, VerifyingKey, VirtualCells},
    poly::{Rotation, commitment::PolynomialCommitmentScheme, kzg::params::ParamsKZG},
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{DefaultPCS, ZkStdLib, ZkStdLibArch};
use num_bigint::BigUint;
use serde_json::Value as Json;

pub type Vk = VerifyingKey<Fq, DefaultPCS>;
/// Advice cells (column, absolute row, value), and whether the values are known.
pub type Witness = Option<(Arc<Vec<(usize, usize, Fq)>>, bool)>;

pub fn hex(bytes: &[u8]) -> String { bytes.iter().map(|b| format!("{b:02x}")).collect() }
pub fn scalar(value: Fq) -> String { BigUint::from_bytes_le(value.to_repr().as_ref()).to_string() }
/// The key's transcript representative as big-endian hex, as `Debug` prints it: the hash of the raw key, the pinned
/// domain and the pinned constraint system (gates, lookups, degree), so it names the whole circuit.
pub fn fingerprint(vk: &Vk) -> String {
    format!("0x{}", hex(&vk.transcript_repr().to_repr().as_ref().iter().rev().copied().collect::<Vec<_>>()))
}
pub fn field(text: &Json) -> Fq { Fq::from_str_vartime(text.as_str().unwrap()).expect("canonical scalar") }
pub fn num(v: &Json) -> usize { v.as_u64().unwrap() as usize }
pub fn list(v: &Json) -> &Vec<Json> { v.as_array().unwrap() }
fn leak(text: &str) -> &'static str { Box::leak(text.to_string().into_boxed_str()) }

#[derive(Clone)]
pub struct Config {
    pub advice: Vec<Column<Advice>>,
    pub fixed: Vec<Column<Fixed>>,
    pub instance: Vec<Column<Instance>>,
    pub selectors: Vec<Selector>,
    pub permutation: Vec<Column<Any>>,
}

impl Config {
    fn column(&self, kind: &str, index: usize) -> Column<Any> {
        match kind {
            "advice" => self.advice[index].into(),
            "fixed" => self.fixed[index].into(),
            "instance" => self.instance[index].into(),
            _ => panic!("column kind {kind}"),
        }
    }

    /// A polynomial built with Rust's operators, as a chip builds it: `+` and `*` fold
    /// `Constant(0)` and `Constant(1)`, so keygen's degree and chunking read the folded tree
    /// (keygen.rs:44, 248) and finalization's rebuild changes nothing.
    fn expr(&self, cells: &mut VirtualCells<'_, Fq>, e: &Json) -> Expression<Fq> {
        let e = list(e);
        let rot = |i: usize| Rotation(e[i].as_i64().unwrap() as i32);
        match e[0].as_str().unwrap() {
            "const" => Expression::Constant(field(&e[1])),
            "sel" => cells.query_selector(self.selectors[num(&e[1])]),
            "advice" => cells.query_advice(self.advice[num(&e[1])], rot(2)),
            "fixed" => cells.query_fixed(self.fixed[num(&e[1])], rot(2)),
            "instance" => cells.query_instance(self.instance[num(&e[1])], rot(2)),
            "neg" => -self.expr(cells, &e[1]),
            "sum" => { let a = self.expr(cells, &e[1]); a + self.expr(cells, &e[2]) }
            "prod" => { let a = self.expr(cells, &e[1]); a * self.expr(cells, &e[2]) }
            "scaled" => self.expr(cells, &e[1]) * field(&e[2]),
            other => panic!("expression node {other}"),
        }
    }
}

#[derive(Clone, Default)]
pub struct Spec(Option<Arc<Json>>);

/// The exported circuit. Its synthesis is one region at row 0, so every
/// region offset is the exported absolute row. `witness` adds advice assignments (proving).
pub struct JsonCircuit<P> { pub spec: Arc<Json>, pub drop_copy: Option<usize>, pub witness: Witness, pub planner: PhantomData<P> }

impl<P: FloorPlanner> Circuit<Fq> for JsonCircuit<P> {
    type Config = Config;
    type FloorPlanner = P;
    type Params = Spec;

    fn without_witnesses(&self) -> Self {
        // The same advice cells with unknown values: V1 measures region shapes on this circuit.
        let witness = self.witness.as_ref().map(|(cells, _)| (cells.clone(), false));
        Self { spec: self.spec.clone(), drop_copy: self.drop_copy, witness, planner: PhantomData }
    }
    fn params(&self) -> Spec { Spec(Some(self.spec.clone())) }
    fn configure(_: &mut ConstraintSystem<Fq>) -> Config { panic!("configure needs the export") }

    fn configure_with_params(meta: &mut ConstraintSystem<Fq>, params: Spec) -> Config {
        let s = params.0.expect("export");
        let advice = (0..num(&s["num_advice"])).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let fixed = (0..num(&s["num_fixed"])).map(|_| meta.fixed_column()).collect::<Vec<_>>();
        let instance = (0..num(&s["num_instance"])).map(|_| meta.instance_column()).collect::<Vec<_>>();
        let selectors = list(&s["selectors"]).iter()
            .map(|simple| if simple.as_bool().unwrap() { meta.selector() } else { meta.complex_selector() })
            .collect();
        let mut config = Config { advice, fixed, instance, selectors, permutation: vec![] };
        config.permutation = list(&s["permutation"]).iter()
            .map(|c| config.column(c[0].as_str().unwrap(), num(&c[1]))).collect();
        // Query indices are registration order, which Lean records at configure
        // time; register all of them in the first closure, before any use.
        let registered = Flag::new(false);
        let register = |config: &Config, cells: &mut VirtualCells<'_, Fq>| {
            if registered.replace(true) { return; }
            for q in list(&s["advice_queries"]) { cells.query_advice(config.advice[num(&q[0])], Rotation(q[1].as_i64().unwrap() as i32)); }
            for q in list(&s["fixed_queries"]) { cells.query_fixed(config.fixed[num(&q[0])], Rotation(q[1].as_i64().unwrap() as i32)); }
            for q in list(&s["instance_queries"]) { cells.query_instance(config.instance[num(&q[0])], Rotation(q[1].as_i64().unwrap() as i32)); }
        };
        if let Some(d) = s["minimum_degree"].as_u64() { meta.set_minimum_degree(d as usize); }
        for gate in list(&s["gates"]) {
            meta.create_gate(leak(gate["name"].as_str().unwrap()), |cells| {
                register(&config, cells);
                let polys: Vec<(String, Expression<Fq>)> = list(&gate["constraints"]).iter()
                    .map(|c| (c["name"].as_str().unwrap().to_string(), config.expr(cells, &c["poly"]))).collect();
                if gate["raw"].as_bool() == Some(true) { Constraints::without_selector(polys) }
                else { Constraints::with_selector(config.selectors[num(&gate["selector"])], polys) }
            });
        }
        for trash in list(&s["trashcans"]) {
            meta.create_gate(leak(trash["name"].as_str().unwrap()), |cells| {
                register(&config, cells);
                Constraints::with_additive_selector(config.selectors[num(&trash["selector"])],
                    list(&trash["constraints"]).iter().map(|p| config.expr(cells, p)).collect())
            });
        }
        for lookup in list(&s["lookups"]) {
            // `None` is the `Constant(1)` Rust stores for it (logup.rs:308).
            let sel = list(&lookup["selector"]);
            let selector = match sel[0].as_str().unwrap() {
                "sel" => Some(config.selectors[num(&sel[1])]),
                "const" if sel[1].as_str() == Some("1") => None,
                _ => panic!("lookup selector {:?}", lookup["selector"]),
            };
            meta.batched_lookup_any(lookup["name"].as_str().unwrap(), selector, |cells| {
                register(&config, cells);
                let inputs = list(&lookup["inputs"]);
                list(&lookup["table"]).iter().enumerate().map(|(w, table)| {
                    (inputs.iter().map(|row| config.expr(cells, &row[w])).collect(), config.expr(cells, table))
                }).collect()
            });
        }
        for &column in &config.permutation { meta.enable_equality(column); }
        for c in list(&s["constants"]) { meta.enable_constant(config.fixed[num(c)]); }
        let queries = |key: &str| list(&s[key]).iter().map(|q| (num(&q[0]), q[1].as_i64().unwrap() as i32)).collect::<Vec<_>>();
        assert_eq!(meta.advice_queries().iter().map(|(c, r)| (c.index(), r.0)).collect::<Vec<_>>(), queries("advice_queries"));
        assert_eq!(meta.fixed_queries().iter().map(|(c, r)| (c.index(), r.0)).collect::<Vec<_>>(), queries("fixed_queries"));
        assert_eq!(meta.instance_queries().iter().map(|(c, r)| (c.index(), r.0)).collect::<Vec<_>>(), queries("instance_queries"));
        config
    }

    fn synthesize(&self, config: Config, mut layouter: impl Layouter<Fq>) -> Result<(), Error> {
        let s = &self.spec;
        layouter.assign_region(|| "export", |mut region| {
            for cell in list(&s["fixed"]) {
                let value = field(&cell[2]);
                region.assign_fixed(|| "", config.fixed[num(&cell[0])], num(&cell[1]), || Value::known(value))?;
            }
            if let Some((cells, known)) = &self.witness {
                for &(column, row, value) in cells.iter() {
                    region.assign_advice(|| "", config.advice[column], row,
                        || if *known { Value::known(value) } else { Value::unknown() })?;
                }
            }
            for (selector, rows) in list(&s["selector_rows"]).iter().enumerate() {
                for row in list(rows) { config.selectors[selector].enable(&mut region, num(row))?; }
            }
            for (i, copy) in list(&s["copies"]).iter().enumerate() {
                if Some(i) == self.drop_copy { continue; }
                let (left, left_row) = (config.permutation[num(&copy[0])], num(&copy[1]));
                let (right, right_row) = (config.permutation[num(&copy[2])], num(&copy[3]));
                // Both endpoints are already absolute, including layouter instance copies.
                let cell = |column, row_offset| Cell { region_index: 0.into(), row_offset, column };
                region.constrain_equal(cell(left, left_row), cell(right, right_row))?;
            }
            Ok(())
        })
    }
}

pub fn arch(a: &Json) -> ZkStdLibArch {
    let b = |key: &str| a[key].as_bool().unwrap();
    ZkStdLibArch { jubjub: b("jubjub"), poseidon: b("poseidon"), sha2_256: b("sha2_256"), sha2_512: b("sha2_512"),
        keccak_256: b("keccak_256"), sha3_256: b("sha3_256"), blake2b: b("blake2b"), secp256k1: b("secp256k1"),
        p256: b("p256"), bls12_381: b("bls12_381"), curve25519: b("curve25519"), base64: b("base64"),
        automaton: b("automaton"), nb_arith_cols: num(&a["nb_arith_cols"]) as u8,
        nr_pow2range_cols: num(&a["nr_pow2range_cols"]) as u8 }
}

/// `MidnightVK::write`'s bytes, written directly: `MidnightVK::read` rebuilds the constraint
/// system from the architecture, so only a stdlib configuration has this format.
pub fn envelope(s: &Json, vk: &Vk, format: SerdeFormat) -> Vec<u8> {
    let mut bytes = vec![];
    arch(&s["architecture"]).write(&mut bytes).unwrap();
    bytes.push(num(&s["k"]) as u8);
    bytes.extend_from_slice(&(num(&s["public_inputs"]) as u32).to_le_bytes());
    vk.write(&mut bytes, format).unwrap();
    bytes
}

/// The Filecoin setup both halves read: `2p13` for k <= 13, else `2p19`, truncated to `2^k`.
pub fn params(spec: &Json, zk: &Path) -> (u32, u32, ParamsKZG<Bls12>) {
    let k = num(&spec["k"]) as u32;
    assert!(k <= 19, "k = {k}: the largest setup is bls_filecoin_2p19");
    let file_k = if k <= 13 { 13 } else { 19 };
    let file = fs::File::open(zk.join(format!("zk_stdlib/examples/assets/bls_filecoin_2p{file_k}"))).unwrap();
    (k, file_k, DefaultPCS::load_params(&mut BufReader::new(file), SerdeFormat::RawBytesUnchecked, k).unwrap())
}

/// The key's raw and processed bytes: `MidnightVK` only for `ZkStdLib::configure(arch, k - 1)`'s
/// pinned system (then `true`), else halo2's.
pub fn key_bytes<P: FloorPlanner>(spec: &Json, planner: &str, circuit: &JsonCircuit<P>, vk: &Vk) -> (bool, Vec<u8>, Vec<u8>) {
    let k = num(&spec["k"]) as u32;
    let mut meta = ConstraintSystem::<Fq>::default();
    JsonCircuit::<P>::configure_with_params(&mut meta, circuit.params());
    let stdlib = planner == "simple" && std::panic::catch_unwind(|| {
        let mut std_meta = ConstraintSystem::<Fq>::default();
        ZkStdLib::configure(&mut std_meta, (arch(&spec["architecture"]), (k - 1) as u8));
        format!("{:?}", std_meta.pinned())
    }).map(|pinned| pinned == format!("{:?}", meta.pinned())).unwrap_or(false);
    let bytes = |format| if stdlib { envelope(spec, vk, format) } else { vk.to_bytes(format) };
    (stdlib, bytes(SerdeFormat::RawBytes), bytes(SerdeFormat::Processed))
}
