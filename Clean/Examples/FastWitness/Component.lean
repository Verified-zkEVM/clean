/-
A segment-generated component whose segment program and witness programs use every construct of the
witness IR, so that fast witness generation can be compared with generation on all of them. Its
circuit only computes witnesses; it constrains nothing.
-/
module

public import Clean.Air.FlatEnsemble
public import Clean.Air.WitnessGeneration

@[expose] public section

namespace FastWitnessExample
open Air.Flat Witgen

variable {p : ℕ} [Fact p.Prime]

/-- Witnesses computed from the row's cell `x`. -/
def main (x : Expression (F p)) : Circuit (F p) Unit := do
  let _bits ← witnessVector 8 (x.bits 8)
  let _inverse ← witnessField (.ite (x =? (0 : F p)) 0 (FExpr.expr x)⁻¹)
  let _shifted ← witnessVector 4
    (.range 4 fun i => ((x.val >>> i) + i * (3 : U64Expr (F p))).toField)
  let _copies ← witnessVector 3 (.envRange 0)
  let _mixed ← witnessVectorProgram 2 do
    let v ← letU (x.val * 7 / 3 % 11)
    let f ← letF (FExpr.expr x * FExpr.expr x + 5)
    return .lit #v[.listGet [f, 1, .expr x] (v % 4),
      .ite (.and (.lt v 5) (.not (.flt f (.expr x)))) (v <<< 2 : U64Expr (F p)).toField
        (f.bit 3)]

def circuit : GeneralFormalCircuit (F p) field unit where
  name := "example"
  main
  Spec _ _ _ := True
  ProverAssumptions _ _ _ := False
  soundness := by simp [circuit_norm, main]
  completeness := by simp [circuit_norm]

/-- The cell `x` of row `i`: segments of three rows, the first from the hint `seed` and the row
index, the others from the previous row. -/
def program : SegmentProgram (F p) where
  Row := field
  length := 3
  first i := pure (FExpr.hintGet "seed" 1 (i / 3) 0 * 3 + (i : U64Expr (F p)).toField)
  next i previous := do
    let v ← letU (previous.val * 5 + i)
    pure (.ite (.feq previous (0 : F p)) 7
      ((v % 1000 : U64Expr (F p)).toField * (FExpr.expr previous)⁻¹))

/-- The component with 16 rows. -/
def component : Component (F p) where
  circuit
  generation := .segments { height := 16, program }

/-- The ensemble of the component, whose prover input is the seeds of its six segments. -/
def ensemble : Ensemble (F p) unit where
  tables := [component]
  unique_names := by simp
  channels := []
  unique_channel_names := by simp
  tables_channels := by simp [circuit_norm, component, circuit]
  verifier_channels := by simp [circuit_norm, Verifier.Program.empty]
  ProverInput := fields 6
  hintTables := [{ key := "seed", width := 1, offset := 0, rows := 6 }]

end FastWitnessExample
