//! Rust half of the lowering replay: configures the exported constraint system through
//! the real `ConstraintSystem` API in a schedule that reproduces Lean's query
//! registration, replays the Clean operation stream through `SimpleFloorPlanner`'s or `V1`'s
//! layouter (so Rust places regions, allocates constants and records copies itself),
//! records what synthesis hands to keygen, and runs `keygen_vk_with_k`.
//! Usage: REPLAY.json SCHEDULE.json MIDNIGHT_ZK OUT_DIR.
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    io::BufReader,
    marker::PhantomData,
    panic::{AssertUnwindSafe, catch_unwind},
    path::Path,
    sync::{Arc, Mutex},
};

use ff::{FromUniformBytes, PrimeField};
use group::Curve;
use midnight_curves::{Bls12, Fq, serde_traits::SerdeObject};
use midnight_proofs::{
    circuit::{Cell, Layouter, SimpleFloorPlanner, Value, floor_planner::V1},
    plonk::{
        Advice, Any, Assignment, Circuit, Column, ConstraintSystem, Constraints, Error, Expression,
        Fixed, FloorPlanner, Instance, Selector, TableColumn, VerifyingKey, VirtualCells,
        keygen_vk_with_k,
    },
    poly::{Rotation, commitment::PolynomialCommitmentScheme, kzg::params::ParamsKZG},
    utils::{SerdeFormat, rational::Rational},
};
use midnight_zk_stdlib::{DefaultPCS, ZkStdLib, ZkStdLibArch};
use num_bigint::BigUint;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};

type Vk = VerifyingKey<Fq, DefaultPCS>;

fn hex(bytes: &[u8]) -> String { bytes.iter().map(|b| format!("{b:02x}")).collect() }
fn scalar(value: Fq) -> String { BigUint::from_bytes_le(value.to_repr().as_ref()).to_string() }
fn field(text: &Json) -> Fq { Fq::from_str_vartime(text.as_str().unwrap()).expect("canonical scalar") }
fn num(v: &Json) -> usize { v.as_u64().unwrap() as usize }
fn rot(v: &Json) -> Rotation { Rotation(v.as_i64().unwrap() as i32) }
fn list(v: &Json) -> &Vec<Json> { v.as_array().unwrap() }
fn text(v: &Json) -> &str { v.as_str().unwrap() }
fn leak(text: &str) -> &'static str { Box::leak(text.to_string().into_boxed_str()) }

#[derive(Clone)]
struct Config {
    advice: Vec<Column<Advice>>,
    fixed: Vec<Column<Fixed>>,
    tables: HashMap<usize, TableColumn>,
    instance: Vec<Column<Instance>>,
    selectors: Vec<Selector>,
    /// Lean's registered queries: a trash atom outside them is an index-free `query_cell`.
    registered: BTreeSet<(String, usize, i64)>,
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

    fn cell(&self, c: &Json) -> Cell {
        let c = list(c);
        Cell { region_index: num(&c[0]).into(), row_offset: num(&c[1]), column: self.column(text(&c[2]), num(&c[3])) }
    }

    /// A query atom, as a closure registers it.
    fn query(&self, cells: &mut VirtualCells<'_, Fq>, q: &Json) -> Option<Expression<Fq>> {
        let q = list(q);
        Some(match text(&q[0]) {
            "advice" => cells.query_advice(self.advice[num(&q[1])], rot(&q[2])),
            "fixed" => cells.query_fixed(self.fixed[num(&q[1])], rot(&q[2])),
            "instance" => cells.query_instance(self.instance[num(&q[1])], rot(&q[2])),
            _ => return None,
        })
    }

    /// A polynomial built the way a chip writes it: with Rust's operators, which fold
    /// `0 + x`, `1 * x` and `0 * x`, from Lean's erased tree (`sum`, `prod`, `scaled`) or a
    /// spelling (`add`, `sub`, `mul`, `scale`). `walked` atoms are `Column::query_cell`s with no
    /// index, which `create_gate` and the lookups register through `query_cells` (a query the
    /// closure made resolves to its index); trash bodies are not walked, so theirs are queried,
    /// except atoms Lean never registers.
    fn expr(&self, cells: &mut VirtualCells<'_, Fq>, e: &Json, walked: bool) -> Expression<Fq> {
        let e = list(e);
        match text(&e[0]) {
            "const" => Expression::Constant(field(&e[1])),
            "sel" => cells.query_selector(self.selectors[num(&e[1])]),
            "advice" | "fixed" | "instance" if walked => self.column(text(&e[0]), num(&e[1])).query_cell(rot(&e[2])),
            "advice" | "fixed" | "instance"
                if !self.registered.contains(&(text(&e[0]).to_string(), num(&e[1]), e[2].as_i64().unwrap())) =>
                self.column(text(&e[0]), num(&e[1])).query_cell(rot(&e[2])),
            "advice" | "fixed" | "instance" => self.query(cells, &Json::Array(e.clone())).unwrap(),
            "neg" => -self.expr(cells, &e[1], walked),
            "sum" | "add" => { let a = self.expr(cells, &e[1], walked); a + self.expr(cells, &e[2], walked) }
            "sub" => { let a = self.expr(cells, &e[1], walked); a - self.expr(cells, &e[2], walked) }
            "prod" | "mul" => { let a = self.expr(cells, &e[1], walked); a * self.expr(cells, &e[2], walked) }
            "scaled" | "scale" => self.expr(cells, &e[1], walked) * field(&e[2]),
            other => panic!("expression node {other}"),
        }
    }
}

/// Fixed columns used as `TableColumn`s: loaded by `assign_table` or a lookup's bare table.
fn table_columns(s: &Json) -> BTreeSet<usize> {
    let mut out: BTreeSet<usize> = list(&s["ops"]).iter().filter_map(|op| op.get("table").map(num)).collect();
    for l in list(&s["cs"]["lookups"]).iter().filter(|l| l["any"].as_bool() != Some(true)) {
        for t in list(&l["table"]) {
            let t = list(t);
            if text(&t[0]) == "fixed" && t[2].as_i64() == Some(0) { out.insert(num(&t[1])); }
        }
    }
    for l in list(&s["cs"]["rejected_lookups"]).iter().filter(|l| l["any"].as_bool() != Some(true)) {
        for c in list(&l["columns"]) {
            let t = list(&list(c)[1]);
            if text(&t[0]) == "fixed" && t[2].as_i64() == Some(0) { out.insert(num(&t[1])); }
        }
    }
    out
}

/// A lookup closure's own queries, in its recorded call order; Rust's `query_cells` registers
/// the rest of its atoms.
fn lookup_atoms(l: &Json) -> Vec<Json> {
    list(&l["queries"]).iter().filter(|q| text(&list(q)[0]) != "sel").cloned().collect()
}

#[derive(Clone, Default)]
struct Spec(Option<Arc<Json>>);

/// The replayed circuit under floor planner `P`.
struct Replay<P> { spec: Arc<Json>, planner: PhantomData<P> }

impl<P> Clone for Replay<P> {
    fn clone(&self) -> Self { Replay { spec: self.spec.clone(), planner: PhantomData } }
}

impl<P: FloorPlanner> Circuit<Fq> for Replay<P> {
    type Config = Config;
    type FloorPlanner = P;
    type Params = Spec;

    fn without_witnesses(&self) -> Self { self.clone() }
    fn params(&self) -> Spec { Spec(Some(self.spec.clone())) }
    fn configure(_: &mut ConstraintSystem<Fq>) -> Config { panic!("configure needs the replay") }

    fn configure_with_params(meta: &mut ConstraintSystem<Fq>, params: Spec) -> Config {
        let s = params.0.expect("replay");
        let cs = &s["cs"];
        let tables = table_columns(&s);
        let advice = (0..num(&cs["num_advice"])).map(|_| meta.advice_column()).collect();
        let registered = [("advice_queries", "advice"), ("fixed_queries", "fixed"), ("instance_queries", "instance")]
            .iter().flat_map(|(key, kind)| list(&cs[*key]).iter()
                .map(|q| (kind.to_string(), num(&q[0]), q[1].as_i64().unwrap())).collect::<Vec<_>>())
            .collect();
        let mut config = Config { advice, fixed: vec![], tables: HashMap::new(), instance: vec![], selectors: vec![], registered };
        for i in 0..num(&cs["num_fixed"]) {
            if tables.contains(&i) {
                let t = meta.lookup_table_column();
                config.fixed.push(t.inner());
                config.tables.insert(i, t);
            } else {
                config.fixed.push(meta.fixed_column());
            }
        }
        config.instance = (0..num(&cs["num_instance"])).map(|_| meta.instance_column()).collect();
        config.selectors = list(&cs["selectors"]).iter()
            .map(|simple| if simple.as_bool().unwrap() { meta.selector() } else { meta.complex_selector() })
            .collect();
        if let Some(d) = cs["minimum_degree"].as_u64() { meta.set_minimum_degree(d as usize); }
        // Batches Lean's builder rejects, first: `BatchedArgument::new` decides them (logup.rs:296-303).
        for l in list(&cs["rejected_lookups"]) {
            let sel = list(&l["selector"]);
            let selector = match text(&sel[0]) {
                "sel" => Some(config.selectors[num(&sel[1])]),
                "const" if text(&sel[1]) == "1" => None,
                _ => panic!("unrepresentable: lookup selector {:?}", l["selector"]),
            };
            let columns = list(&l["columns"]);
            let inputs = |config: &Config, cells: &mut VirtualCells<'_, Fq>, c: &Json| -> Vec<Expression<Fq>> {
                list(&list(c)[0]).iter().map(|e| config.expr(cells, e, true)).collect()
            };
            let name = text(&l["name"]);
            if l["any"].as_bool() == Some(true) {
                meta.batched_lookup_any(name, selector, |cells| columns.iter()
                    .map(|c| (inputs(&config, cells, c), config.expr(cells, &list(c)[1], true))).collect());
            } else {
                meta.batched_lookup(name, selector, |cells| columns.iter()
                    .map(|c| (inputs(&config, cells, c), config.tables[&num(&list(&list(c)[1])[1])])).collect());
            }
        }
        let schedule = &s["schedule"];
        // Without a registering schedule, Lean's query lists are registered in the first
        // closure, as the vk-export tool does; the report says so.
        let mut forced = schedule["forced"].as_bool().unwrap();
        let mut preregister = |config: &Config, cells: &mut VirtualCells<'_, Fq>| {
            if !forced { return; }
            forced = false;
            for (key, kind) in [("advice_queries", "advice"), ("fixed_queries", "fixed"), ("instance_queries", "instance")] {
                for q in list(&cs[key]) { config.query(cells, &json!([kind, q[0], q[1]])); }
            }
        };
        for event in list(&schedule["events"]) {
            let (kind, i) = (text(&event[0]), num(&event[1]));
            match kind {
                "gate" | "trash" => {
                    let g = &cs[if kind == "gate" { "gates" } else { "trashcans" }][i];
                    meta.create_gate(leak(text(&g["name"])), |cells| {
                        preregister(&config, cells);
                        for q in list(&g["queries"]) { config.query(cells, q); }
                        let polys: Vec<(String, Expression<Fq>)> = list(&g["constraints"]).iter()
                            .map(|c| (text(&c["name"]).to_string(), config.expr(cells, &c["poly"], kind == "gate"))).collect();
                        if g["raw"].as_bool() == Some(true) { return Constraints::without_selector(polys); }
                        let selector = config.selectors[num(&g["selector"])];
                        if kind == "gate" { Constraints::with_selector(selector, polys) }
                        else { Constraints::with_additive_selector(selector, polys) }
                    });
                }
                "lookup" => {
                    let l = &cs["lookups"][i];
                    // `None` is the `Constant(1)` Rust stores for it (logup.rs:308).
                    let sel = list(&l["selector"]);
                    let selector = match text(&sel[0]) {
                        "sel" => Some(config.selectors[num(&sel[1])]),
                        "const" if text(&sel[1]) == "1" => None,
                        _ => panic!("unrepresentable: lookup selector {:?}", l["selector"]),
                    };
                    let (inputs, table) = (list(&l["inputs"]), list(&l["table"]));
                    let bare: Option<Vec<TableColumn>> = if l["any"].as_bool() == Some(true) { None } else {
                        table.iter().map(|t| {
                            let t = list(t);
                            (text(&t[0]) == "fixed" && t[2].as_i64() == Some(0)).then(|| config.tables[&num(&t[1])])
                        }).collect()
                    };
                    let own = lookup_atoms(l);
                    let columns = |config: &Config, cells: &mut VirtualCells<'_, Fq>| -> Vec<Vec<Expression<Fq>>> {
                        (0..table.len()).map(|w| inputs.iter().map(|row| config.expr(cells, &list(row)[w], true)).collect()).collect()
                    };
                    let name = text(&l["name"]);
                    match bare {
                        Some(tcs) => { meta.batched_lookup(name, selector, |cells| {
                            preregister(&config, cells);
                            for q in &own { config.query(cells, q); }
                            columns(&config, cells).into_iter().zip(tcs).collect()
                        }); }
                        None => { meta.batched_lookup_any(name, selector, |cells| {
                            preregister(&config, cells);
                            for q in &own { config.query(cells, q); }
                            let ins = columns(&config, cells);
                            let ts: Vec<_> = table.iter().map(|t| config.expr(cells, t, true)).collect();
                            ins.into_iter().zip(ts).collect()
                        }); }
                    }
                }
                "equality" => {
                    let c = list(&cs["permutation"][i]);
                    meta.enable_equality(config.column(text(&c[0]), num(&c[1])));
                }
                "constant" => meta.enable_constant(config.fixed[num(&cs["constants"][i])]),
                other => panic!("schedule event {other}"),
            }
        }
        config
    }

    fn synthesize(&self, config: Config, mut layouter: impl Layouter<Fq>) -> Result<(), Error> {
        let mut region_index = 0usize;
        for op in list(&self.spec["ops"]) {
            if op.get("region").is_some() {
                // The recorder reads the region index from the name (V1 reports no starts).
                let (body, current) = (list(&op["ops"]), region_index);
                region_index += 1;
                layouter.assign_region(|| format!("#{current}"), |mut region| {
                    for o in body {
                        let o = list(o);
                        match text(&o[0]) {
                            "advice" => { region.assign_advice(|| "", config.advice[num(&o[1])], num(&o[2]), || Value::<Fq>::unknown())?; }
                            "fixed" => {
                                let v = field(&o[3]);
                                region.assign_fixed(|| "", config.fixed[num(&o[1])], num(&o[2]), || Value::known(v))?;
                            }
                            "gate" => config.selectors[num(&o[1])].enable(&mut region, num(&o[2]))?,
                            "lookup" => for s in list(&o[1]) { config.selectors[num(s)].enable(&mut region, num(&o[2]))?; },
                            "equal" => region.constrain_equal(config.cell(&o[1]), config.cell(&o[2]))?,
                            "constant" => region.constrain_constant(config.cell(&o[1]), field(&o[2]))?,
                            "instance" => {
                                // Rust's only in-region instance copy is `assign_advice_from_instance`.
                                let c = list(&o[1]);
                                assert!(num(&c[0]) == current && text(&c[2]) == "advice",
                                    "unrepresentable: in-region instance copy of a cell outside this region or not advice");
                                region.assign_advice_from_instance(|| "", config.instance[num(&o[2])], num(&o[3]),
                                    config.advice[num(&c[3])], num(&c[1]))?;
                            }
                            other => panic!("region operation {other}"),
                        }
                    }
                    Ok(())
                })?;
            } else if let Some(i) = op.get("instance") {
                let i = list(i);
                layouter.constrain_instance(config.cell(&i[0]), config.instance[num(&i[1])], num(&i[2]))?;
            } else if let Some(t) = op.get("table") {
                let (column, values) = (config.tables[&num(t)], list(&op["values"]));
                layouter.assign_table(|| "", |mut table| {
                    for (row, v) in values.iter().enumerate() {
                        let v = field(v);
                        table.assign_cell(|| "", column, row, || Value::known(v))?;
                    }
                    Ok(())
                })?;
            } else {
                panic!("operation {op}");
            }
        }
        Ok(())
    }
}

/// What synthesis hands to keygen's `Assembly`, in order, and each region's first assigned or
/// enabled absolute row (`first_rows`), from which V1's starts are read.
struct Recorder { usable: usize, fixed: BTreeMap<(usize, usize), Fq>, selectors: BTreeMap<usize, BTreeSet<usize>>,
    copies: Vec<(Column<Any>, usize, Column<Any>, usize)>, unknown_fixed: usize,
    region: Option<usize>, first_rows: BTreeMap<usize, usize> }

impl Recorder {
    fn row(&mut self, row: usize) {
        if let Some(r) = self.region { self.first_rows.entry(r).or_insert(row); }
    }
}

fn known<VR: Into<Rational<Fq>>>(v: Value<VR>) -> Option<Fq> {
    let mut out = None;
    v.map(|x| { let r: Rational<Fq> = x.into(); out = Some(r.evaluate()); });
    out
}

impl Assignment<Fq> for Recorder {
    fn enter_region<NR, N>(&mut self, name: N) where NR: Into<String>, N: FnOnce() -> NR {
        self.region = name().into().strip_prefix('#').and_then(|i| i.parse().ok());
    }
    fn annotate_column<A, AR>(&mut self, _: A, _: Column<Any>) where A: FnOnce() -> AR, AR: Into<String> {}
    fn exit_region(&mut self) { self.region = None; }
    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where A: FnOnce() -> AR, AR: Into<String> {
        self.row(row);
        self.selectors.entry(selector.index()).or_default().insert(row);
        Ok(())
    }
    fn query_instance(&self, _: Column<Instance>, _: usize) -> Result<Value<Fq>, Error> { Ok(Value::unknown()) }
    fn assign_advice<V, VR, A, AR>(&mut self, _: A, _: Column<Advice>, row: usize, _: V) -> Result<(), Error>
    where V: FnOnce() -> Value<VR>, VR: Into<Rational<Fq>>, A: FnOnce() -> AR, AR: Into<String> { self.row(row); Ok(()) }
    fn assign_fixed<V, VR, A, AR>(&mut self, _: A, column: Column<Fixed>, row: usize, to: V) -> Result<(), Error>
    where V: FnOnce() -> Value<VR>, VR: Into<Rational<Fq>>, A: FnOnce() -> AR, AR: Into<String> {
        self.row(row);
        match known(to()) {
            Some(v) => { self.fixed.insert((column.index(), row), v); }
            None => self.unknown_fixed += 1,
        }
        Ok(())
    }
    fn copy(&mut self, lc: Column<Any>, lr: usize, rc: Column<Any>, rr: usize) -> Result<(), Error> {
        self.copies.push((lc, lr, rc, rr));
        Ok(())
    }
    fn fill_from_row(&mut self, column: Column<Fixed>, row: usize, to: Value<Rational<Fq>>) -> Result<(), Error> {
        let v = known(to).expect("known table default");
        for r in row..self.usable { self.fixed.insert((column.index(), r), v); }
        Ok(())
    }
    fn push_namespace<NR, N>(&mut self, _: N) where NR: Into<String>, N: FnOnce() -> NR {}
    fn pop_namespace(&mut self, _: Option<String>) {}
}

fn arch(a: &Json) -> ZkStdLibArch {
    let b = |key: &str| a[key].as_bool().unwrap();
    ZkStdLibArch { jubjub: b("jubjub"), poseidon: b("poseidon"), sha2_256: b("sha2_256"), sha2_512: b("sha2_512"),
        keccak_256: b("keccak_256"), sha3_256: b("sha3_256"), blake2b: b("blake2b"), secp256k1: b("secp256k1"),
        p256: b("p256"), bls12_381: b("bls12_381"), curve25519: b("curve25519"), base64: b("base64"),
        automaton: b("automaton"), nb_arith_cols: num(&a["nb_arith_cols"]) as u8,
        nr_pow2range_cols: num(&a["nr_pow2range_cols"]) as u8 }
}

/// `nb_public_inputs` as the native chip counts it: one per `constrain_as_public_input`, which is
/// one layouter `constrain_instance` on instance column 1 (native_chip.rs:645-653). Counted over the
/// layouter instance copies this replay makes, not read from Lean's export.
fn public_inputs(s: &Json) -> u32 {
    list(&s["ops"]).iter().filter(|op| op.get("instance").map_or(false, |i| num(&list(i)[1]) == 1)).count() as u32
}

/// `MidnightVK::write`'s bytes, written directly (see vk-export).
fn envelope(s: &Json, vk: &Vk, format: SerdeFormat) -> Vec<u8> {
    let mut bytes = vec![];
    arch(&s["architecture"]).write(&mut bytes).unwrap();
    bytes.push(num(&s["k"]) as u8);
    bytes.extend_from_slice(&public_inputs(s).to_le_bytes());
    vk.write(&mut bytes, format).unwrap();
    bytes
}

fn kind(c: &Column<Any>) -> &'static str {
    match c.column_type() { Any::Advice => "advice", Any::Fixed => "fixed", Any::Instance => "instance" }
}

/// The configured system as the replay's JSON spells it.
fn configured(meta: &ConstraintSystem<Fq>) -> Json {
    json!({
        "advice_queries": meta.advice_queries().iter().map(|(c, r)| json!([c.index(), r.0])).collect::<Vec<_>>(),
        "fixed_queries": meta.fixed_queries().iter().map(|(c, r)| json!([c.index(), r.0])).collect::<Vec<_>>(),
        "instance_queries": meta.instance_queries().iter().map(|(c, r)| json!([c.index(), r.0])).collect::<Vec<_>>(),
        "permutation": meta.permutation().get_columns().iter().map(|c| json!([kind(c), c.index()])).collect::<Vec<_>>(),
        "constants": meta.constants().iter().map(|c| c.index()).collect::<Vec<_>>(),
    })
}

/// Each region's offset of its first operation that assigns or enables a row, in the order
/// Rust's region calls reach the `Assignment`; `None` for a region with none (Rust measures no
/// column for it, so both planners start it at 0).
fn first_offsets(spec: &Json) -> Vec<Option<usize>> {
    list(&spec["ops"]).iter().filter_map(|op| op.get("ops")).map(|body| list(body).iter().find_map(|o| {
        let o = list(o);
        match text(&o[0]) {
            "advice" | "fixed" | "gate" => Some(num(&o[2])),
            "lookup" if !list(&o[1]).is_empty() => Some(num(&o[2])),
            "instance" => Some(num(&list(&o[1])[1])),
            _ => None,
        }
    })).collect()
}

fn run(spec: Json, zk: &Path, report: &mut serde_json::Map<String, Json>) -> Result<(), String> {
    report.insert("planner".into(), spec["planner"].clone());
    if spec["planner"].as_str() == Some("v1") { run_with::<V1>(spec, zk, report) }
    else { run_with::<SimpleFloorPlanner>(spec, zk, report) }
}

fn run_with<P: FloorPlanner>(spec: Json, zk: &Path, report: &mut serde_json::Map<String, Json>) -> Result<(), String> {
    let k = num(&spec["k"]) as u32;
    let spec = Arc::new(spec);
    let circuit = Replay::<P> { spec: spec.clone(), planner: PhantomData };
    let mut meta = ConstraintSystem::<Fq>::default();
    let config = Replay::<P>::configure_with_params(&mut meta, circuit.params());
    report.insert("configured".into(), configured(&meta));
    // `MidnightVK::read` rebuilds the constraint system from the architecture alone, so only a
    // system with `ZkStdLib::configure(arch, k - 1)`'s pinned form has a `MidnightVK`.
    let stdlib = catch_unwind(AssertUnwindSafe(|| {
        let mut std_meta = ConstraintSystem::<Fq>::default();
        ZkStdLib::configure(&mut std_meta, (arch(&spec["architecture"]), (k - 1) as u8));
        format!("{:?}", std_meta.pinned())
    }));
    *PANIC_AT.lock().unwrap_or_else(|e| e.into_inner()) = None;
    // `setup_vk`'s `MidnightCircuit` lays out with `SimpleFloorPlanner` (interface.rs:386); a V1
    // layout is keyed only through a custom `Circuit` and `VerifyingKey::write`.
    let stdlib = spec["planner"].as_str() != Some("v1")
        && stdlib.map(|pinned| pinned == format!("{:?}", meta.pinned())).unwrap_or(false);
    report.insert("format".into(), json!(if stdlib { "midnight" } else { "halo2" }));
    let n = 1usize << k;
    let usable = n.saturating_sub(meta.blinding_factors() + 1);
    let mut rec = Recorder { usable, fixed: BTreeMap::new(), selectors: BTreeMap::new(), copies: vec![], unknown_fixed: 0,
        region: None, first_rows: BTreeMap::new() };
    let captured = P::synthesize_capturing_regions(&mut rec, &circuit, config, meta.constants().clone())
        .map_err(|e| format!("synthesis: {e:?}"))?;
    let starts: Vec<usize> = match captured {
        Some(starts) => starts.iter().map(|s| **s).collect(),
        None => first_offsets(&spec).iter().enumerate()
            .map(|(i, offset)| offset.map_or(0, |o| rec.first_rows[&i] - o)).collect(),
    };
    let perm = meta.permutation().get_columns();
    let pos = |c: &Column<Any>| perm.iter().position(|p| p == c).unwrap_or(9999);
    report.insert("derived".into(), json!({
        "region_starts": starts,
        "fixed": rec.fixed.iter().filter(|(_, v)| **v != Fq::from(0u64)).map(|((c, r), v)| json!([c, r, scalar(*v)])).collect::<Vec<_>>(),
        "selector_rows": (0..meta.num_selectors()).map(|i| rec.selectors.get(&i).map(|s| s.iter().copied().collect()).unwrap_or_default())
            .collect::<Vec<Vec<usize>>>(),
        "copies": rec.copies.iter().map(|(lc, lr, rc, rr)| json!([pos(lc), lr, pos(rc), rr])).collect::<Vec<_>>(),
        "unknown_fixed": rec.unknown_fixed,
    }));

    let file_k = if k <= 13 { 13 } else { 19 };
    let file = fs::File::open(zk.join(format!("zk_stdlib/examples/assets/bls_filecoin_2p{file_k}"))).unwrap();
    let params: ParamsKZG<Bls12> = DefaultPCS::load_params(&mut BufReader::new(file), SerdeFormat::RawBytesUnchecked, k).unwrap();
    let start = std::time::Instant::now();
    let vk = keygen_vk_with_k::<Fq, DefaultPCS, _>(&params, &circuit, k).map_err(|e| format!("keygen: {e:?}"))?;
    let keygen = start.elapsed().as_millis();
    let bytes = |format| if stdlib { envelope(&spec, &vk, format) } else { vk.to_bytes(format) };
    let raw = bytes(SerdeFormat::RawBytes);
    let processed = bytes(SerdeFormat::Processed);
    let inner = vk.to_bytes(SerdeFormat::RawBytes);
    let domain = format!("{:?}", vk.get_domain().pinned());
    let pinned = format!("{:?}", vk.cs().pinned());
    let transcript = [inner, domain.into_bytes(), pinned.clone().into_bytes()].concat();
    let hash = blake2b_simd::Params::new().hash_length(64).personal(b"Halo2-Verify-Key").hash(&transcript);
    assert_eq!(Fq::from_uniform_bytes(hash.as_array()), vk.transcript_repr(), "rebuilt transcript input");
    let digest = Sha256::digest(&raw);
    let static_vks = fs::read_dir(zk.join("zk_stdlib/tests/static_vks")).unwrap()
        .map(|e| e.unwrap().path()).filter(|p| fs::read(p).unwrap() == digest[..])
        .map(|p| p.file_name().unwrap().to_string_lossy().into_owned()).collect::<Vec<_>>();
    let cs = vk.cs();
    let points = vk.phase0_commitment().0.iter().map(|c| hex(&c.as_point().to_affine().to_raw_bytes())).collect::<Vec<_>>();
    report.insert("static_vks".into(), json!(static_vks));
    report.insert("key".into(), json!({"format": if stdlib { "midnight" } else { "halo2" }, "points": points, "raw": hex(&raw), "processed": hex(&processed),
        "transcript_input": hex(&transcript), "transcript_repr": scalar(vk.transcript_repr()), "pinned_cs": pinned,
        "degree": cs.degree(), "blinding_factors": cs.blinding_factors(), "num_fixed": cs.num_fixed_columns(),
        "permutation_columns": cs.permutation().get_columns().len()}));
    report.insert("ms".into(), json!({"keygen": keygen}));
    Ok(())
}

/// Where the first panic was raised: the harness's own source, or Rust's.
static PANIC_AT: Mutex<Option<String>> = Mutex::new(None);

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let [_, replay, schedule, zk, out] = &args[..] else { panic!("usage: REPLAY.json SCHEDULE.json MIDNIGHT_ZK OUT_DIR") };
    let mut spec: Json = serde_json::from_slice(&fs::read(replay).unwrap()).unwrap();
    spec["schedule"] = serde_json::from_slice(&fs::read(schedule).unwrap()).unwrap();
    let mut report = serde_json::Map::new();
    report.insert("schema".into(), json!("midnight-lowering-rust-v1"));
    std::panic::set_hook(Box::new(|info| {
        let mut at = PANIC_AT.lock().unwrap_or_else(|e| e.into_inner());
        if at.is_none() { *at = Some(info.location().map(|l| format!("{}:{}", l.file(), l.line())).unwrap_or_default()); }
    }));
    let outcome = catch_unwind(AssertUnwindSafe(|| run(spec, Path::new(zk), &mut report)));
    // `rust`: an API returned an error or Rust's own code panicked. `unrepresentable`: the
    // stream has no Rust API spelling. `harness`: a harness limitation or bug.
    let (error, kind) = match outcome {
        Ok(Ok(())) => (None, None),
        Ok(Err(e)) => (Some(e), Some("rust")),
        Err(p) => {
            let message = p.downcast_ref::<String>().cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_default();
            let at = PANIC_AT.lock().unwrap_or_else(|e| e.into_inner()).clone().unwrap_or_default();
            let kind = if message.starts_with("unrepresentable:") { "unrepresentable" }
                else if at.starts_with("src/main.rs") || at.is_empty() { "harness" } else { "rust" };
            (Some(format!("panic at {at}: {message}")), Some(kind))
        }
    };
    println!("rust: {}{}", kind.map(|k| format!("{k}: ")).unwrap_or_default(), error.as_deref().unwrap_or("keygen ok"));
    report.insert("error".into(), json!(error));
    report.insert("error_kind".into(), json!(kind));
    fs::write(Path::new(out).join("rust.json"), serde_json::to_vec_pretty(&report).unwrap()).unwrap();
}
