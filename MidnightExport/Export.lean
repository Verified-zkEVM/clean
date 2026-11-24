import Midnight.Chips.CertifiedCircuit
import Midnight.Chips.Canonical
import Midnight.Chips.KeyChecks
import Midnight.Chips.Usize
import Midnight.Keygen.Pipeline
import Midnight.SHA256.SynthesisLayout
import Midnight.SHA256.Configure

/-! Export of a circuit for the Rust half of the VK comparison (`scripts/vk-export`), and
Lean's own key for it. The JSON is what halo2's `configure` and keygen synthesis consume:
columns, selectors, the query registration order, gate bodies, lookups and additive gates as
Rust expression trees (which Rust rebuilds with its operators), the equality and constant columns,
the minimum degree, and every fixed cell, selector row and copy at its absolute row. -/

namespace Midnight.Export
open Lean Halo2 Midnight.Keygen Midnight.Chips

/-- Rust's V1 planner for `source`, filling its constants columns. -/
def v1 (source : CS) : Layout.Planner := .v1 source.constantColumns.toList

/-- The layout the key is derived from: Rust's `usize` lowering of `Canonical.rustOps`. -/
def layout (source : CS) (ops : Operations F) (k : Nat) (planner : Layout.Planner := .simple) :
    Layout.DerivedLayout :=
  Usize.layout source (Canonical.rustOps source ops) k planner

/-- Keygen's bounds on that lowering; `dense` would silently drop an out-of-range write. -/
def checkLayout (source : CS) (ops : Operations F) (k : Nat)
    (planner : Layout.Planner := .simple) : Except String Unit :=
  Usize.check source (Canonical.rustOps source ops) k planner

/-- `Keygen.deriveFromCertificate`'s checks on `ops`, the stream a certificate is for, then whether
the exported layout (of `Canonical.rustOps`) is the one it derives the key from. Each is `none`
when it holds, else why not. -/
def certifiedChecks (source : CS) (ops : Operations F) (k : Nat) (planner : Layout.Planner) :
    List (String × Option String) :=
  let usize : Option String := match Usize.check source ops k planner with
    | .ok _ => none
    | .error e => some e
  let keyed : Option String := if usize.isSome then some "not run: usize_check failed"
    else if KeyChecks.keyed source ops k planner then none
    else some "the key's layout is not the certified one, fixed writes conflict or a constant \
      is unplaced"
  let same : Option String :=
    if decide (Usize.layout source ops k planner = layout source ops k planner) then none
    else some "the exported layout (Rust's reading of the stream) is not the stream's own"
  [("usize_check", usize), ("keyed", keyed), ("key_layout", same)]

private def queryJson (kind : String) (queries : Array (Nat × Int)) (i : Nat) : Except String Json :=
  match queries[i]? with
  | some (column, rotation) => pure (Json.arr #[kind, column, rotation])
  | none => throw s!"unregistered {kind} query {i}"

/-- One erased polynomial (`CS.rich`, Rust's node shapes), queries by `(column, rotation)`. -/
def exprJson (s : CS) : RichExpression F → Except String Json
  | .constant c => pure (Json.arr #["const", toString (scalarNat c)])
  | .selector i => pure (Json.arr #["sel", i])
  | .advice i => queryJson "advice" s.adviceQueries i
  | .fixed i => queryJson "fixed" s.fixedQueries i
  | .instance i => queryJson "instance" s.instanceQueries i
  | .negated a => return Json.arr #["neg", ← exprJson s a]
  | .sum a b => return Json.arr #["sum", ← exprJson s a, ← exprJson s b]
  | .product a b => return Json.arr #["prod", ← exprJson s a, ← exprJson s b]
  | .scaled a c => return Json.arr #["scaled", ← exprJson s a, toString (scalarNat c)]

private def pairs (xs : Array (Nat × Int)) : Json :=
  Json.arr (xs.map fun (c, r) => Json.arr #[c, r])

private def kindName : ColumnKind → String
  | .advice => "advice"
  | .fixed => "fixed"
  | .instance => "instance"

def architectureJson (a : Architecture) : Json :=
  Json.mkObj [("jubjub", a.jubjub), ("poseidon", a.poseidon), ("sha2_256", a.sha2_256),
    ("sha2_512", a.sha2_512), ("keccak_256", a.keccak_256), ("sha3_256", a.sha3_256),
    ("blake2b", a.blake2b), ("secp256k1", a.secp256k1), ("p256", a.p256),
    ("bls12_381", a.bls12_381), ("curve25519", a.curve25519), ("base64", a.base64),
    ("automaton", a.automaton), ("nb_arith_cols", a.nbArithCols.toNat),
    ("nr_pow2range_cols", a.nrPow2rangeCols.toNat)]

def circuitJson (architecture : Architecture) (publicInputs : UInt32) (source : CS) (k : Nat)
    (l : Layout.DerivedLayout) (planner : Layout.Planner := .simple) : Except String Json := do
  let expr := fun e => exprJson source (source.rich e)
  let gates ← (source.gates.filter (!·.constraints.isEmpty)).mapM fun g => do
    return Json.mkObj [("name", g.name), ("selector", g.selector.index), ("raw", g.raw),
      ("constraints", Json.arr (← g.constraints.mapM
        fun (name, p) => return Json.mkObj [("name", name), ("poly", ← expr p)]))]
  let trashcans ← source.trashcans.mapM fun g => do
    return Json.mkObj [("name", g.name), ("selector", g.selector.index),
      ("constraints", Json.arr (← g.constraints.mapM fun (_, p) => expr p))]
  let lookups ← source.lookups.mapM fun lookup => do
    return Json.mkObj [("name", lookup.name), ("selector", ← expr lookup.selector),
      ("inputs", Json.arr (← lookup.inputs.mapM fun row => return Json.arr (← row.mapM expr))),
      ("table", Json.arr (← lookup.table.mapM expr))]
  let mut fixed : Array Json := #[]
  for column in [0:source.numFixed] do
    for (value, row) in (l.fixed[column]?.getD #[]).zipIdx do
      if value != 0 then fixed := fixed.push (Json.arr #[column, row, toString value])
  return Json.mkObj [
    ("schema", "midnight-vk-export-v1"), ("k", k),
    ("planner", match planner with | .simple => "simple" | .v1 _ => "v1"),
    ("architecture", architectureJson architecture), ("public_inputs", publicInputs.toNat),
    ("num_advice", source.numAdvice), ("num_fixed", source.numFixed),
    ("num_instance", source.numInstance),
    ("selectors", toJson ((Array.range source.numSelectors).map source.selectorSimple)),
    ("advice_queries", pairs source.adviceQueries), ("fixed_queries", pairs source.fixedQueries),
    ("instance_queries", pairs source.instanceQueries),
    ("permutation", Json.arr (source.permutation.map fun c => Json.arr #[kindName c.kind, c.index])),
    ("constants", toJson source.constantColumns), ("minimum_degree", toJson source.minimumDegree),
    ("gates", Json.arr gates), ("trashcans", Json.arr trashcans), ("lookups", Json.arr lookups),
    ("fixed", Json.arr fixed), ("selector_rows", toJson l.selectorRows),
    ("copies", Json.arr (l.copies.toArray.map fun (a, b, c, d) => Json.arr #[a, b, c, d])),
    ("region_starts", toJson l.regionStarts)]

def formatJson : VKFormat → Json
  | .midnight .. => "midnight"
  | .halo2 => "halo2"

def keyJson (key : DerivedVK) (finalized : CS) : Json :=
  Json.mkObj [("format", formatJson key.format),
    ("points", toJson (key.commitments.map fun point => Blake2b.hex (G1.encodeRaw point))),
    ("raw", Blake2b.hex key.raw), ("processed", Blake2b.hex key.processed),
    ("transcript_input", Blake2b.hex key.transcript), ("transcript_repr", toString key.transcriptRepr),
    ("pinned_cs", finalized.pinnedDebug), ("degree", finalized.degree),
    ("blinding_factors", finalized.blindingFactors), ("num_fixed", finalized.numFixed),
    ("permutation_columns", finalized.permutation.size)]

/-- The first `2^k` monomial points of a halo2 `ParamsKZG` file in `RawBytes` layout (as the
Filecoin assets): `k` as u32, then the points. Rust loads them unchecked, so only the curve
equation and canonical encoding are checked here. -/
def readSrs (path : System.FilePath) (k : Nat) : IO (Array G1.Point) := do
  let handle ← IO.FS.Handle.mk path .read
  let n := 2 ^ k
  let mut bytes := ByteArray.empty
  while bytes.size < 4 + 96 * n do
    let chunk ← handle.read (USize.ofNat (4 + 96 * n - bytes.size))
    if chunk.isEmpty then throw (IO.userError s!"{path} has fewer than 2^{k} points")
    bytes := bytes ++ chunk
  unless (bytes.extract 0 4).data.foldr (fun byte v => v * 256 + byte.toNat) 0 ≥ k do
    throw (IO.userError s!"{path} is smaller than 2^{k}")
  let be := fun (b : ByteArray) => b.data.foldl (fun v byte => v * 256 + byte.toNat) 0
  (Array.range n).mapM fun i => do
    let raw := bytes.extract (4 + 96 * i) (4 + 96 * i + 96)
    let some point := G1.ofCoords? (be (raw.extract 0 48)) (be (raw.extract 48 96))
      | throw (IO.userError s!"setup point {i} is off the curve")
    unless G1.encodeRaw point == raw do throw (IO.userError s!"setup point {i} is not canonical")
    pure point

/-- `export.json`, then Lean's key for the same layout on the Filecoin setup in `ASSETS_DIR`
(`lean.json`, `lean.{raw,processed}.bin`). `--corrupt-fixed COLUMN ROW` changes one cell of the
fixed matrix (selector columns included) for the derivation only: a negative test. -/
def main (source : CS) (k : Nat) (ops : Operations F) (args : List String)
    (architecture : Architecture := SHA256.architecture) (planner : Layout.Planner := .simple) :
    IO UInt32 := do
  let (out, assets, corrupt) ← match args with
    | [out, assets] => pure (out, assets, none)
    | [out, assets, "--corrupt-fixed", c, r] => pure (out, assets, some (c.toNat!, r.toNat!))
    | _ => throw (IO.userError "usage: OUT_DIR ASSETS_DIR [--corrupt-fixed COLUMN ROW]")
  let out : System.FilePath := out
  unless k ≤ 19 do
    throw (IO.userError s!"k = {k}: the exporter's largest setup is bls_filecoin_2p19")
  -- The Rust half loads the same file for the same `k`.
  let srsName := s!"bls_filecoin_2p{if k ≤ 13 then 13 else 19}"
  let srsPath := (assets : System.FilePath) / srsName
  let start ← IO.monoMsNow
  IO.ofExcept source.validate
  let l := layout source ops k planner
  IO.ofExcept (checkLayout source ops k planner)
  let laid ← IO.monoMsNow
  IO.FS.writeFile (out / "export.json") (← IO.ofExcept (circuitJson architecture (publicInputCount ops) source k l planner)).compress
  let exported ← IO.monoMsNow
  let srs ← readSrs srsPath k
  let read ← IO.monoMsNow
  let fixed := match corrupt with
    | none => l.fixed
    | some (c, r) => l.fixed.modify c fun column =>
        column.modify r fun v => (v + 1) % BLS12_381.scalarFieldSize
  let key ← IO.ofExcept (deriveVK architecture k planner ops source fixed l.copies srs)
  let derived ← IO.monoMsNow
  IO.FS.writeBinFile (out / "lean.raw.bin") key.raw
  IO.FS.writeBinFile (out / "lean.processed.bin") key.processed
  IO.FS.writeFile (out / "lean.json") (Json.pretty (Json.mkObj [
    ("schema", "midnight-vk-export-lean-v1"), ("k", k), ("srs", srsName), ("corrupt_fixed", toJson corrupt),
    ("key", keyJson key source.finalize),
    ("ms", Json.mkObj [("layout", laid - start), ("export", exported - laid), ("srs", read - exported),
      ("derive", derived - read)])]))
  IO.println s!"lean: layout {laid - start} ms, export {exported - laid} ms, key derived in {derived - read} ms"
  return 0

end Midnight.Export
