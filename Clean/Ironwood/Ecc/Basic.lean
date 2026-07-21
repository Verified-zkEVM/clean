import Clean.Halo2
import Clean.Circuit
import Clean.Utils.Tactics
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.Defs

namespace Halo2.Ironwood

theorem Point.eval_eq (env : Placed Environment Fp) (point : Point (AssignedCell Fp)) :
    eval env point = { x := eval env point.x, y := eval env point.y } := by
  simp only [circuit_norm, explicit_provable_type]

theorem Point.eval_eq_prover (env : Placed ProverEnvironment Fp) (point : Point (AssignedCell Fp)) :
    eval env point = { x := eval env point.x, y := eval env point.y } := by
  simp only [circuit_norm, explicit_provable_type]

/-- Witgen (prover-program) evaluation of a `Point` is componentwise. -/
theorem Point.witgen_eval_eq (ctx : Witgen.CtxOver Fp (Placed ProverEnvironment Fp))
    (point : Point (Witgen.FExprOver Fp (AssignedCell Fp))) :
    Witgen.eval ctx point = { x := Witgen.FExprOver.eval ctx point.x, y := Witgen.FExprOver.eval ctx point.y } := by
  simp only [circuit_norm, explicit_provable_type]
end Halo2.Ironwood
