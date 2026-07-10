import Clean.Halo2
import Clean.Circuit
import Clean.Utils.Tactics
import Clean.Orchard.Specs.Pallas

namespace Halo2.Ironwood
abbrev Fp := Orchard.Fp
abbrev pallasB := Orchard.pallasB

abbrev Point := Orchard.Point

instance : ProvableType Point where
  size := 2
  toElements point := #v[point.x, point.y]
  fromElements elems := { x := elems[0], y := elems[1] }

theorem Point.eval_eq (env : Placed Environment Fp) (point : Point (AssignedCell Fp)) :
    eval env point = { x := eval env point.x, y := eval env point.y } := by
  with_unfolding_all rfl

theorem Point.eval_eq_prover (env : Placed ProverEnvironment Fp) (point : Point (AssignedCell Fp)) :
    eval env point = { x := eval env point.x, y := eval env point.y } := by
  with_unfolding_all rfl

/-- Witgen (prover-program) evaluation of a `Point` is componentwise. -/
theorem Point.witgen_eval_eq (ctx : Witgen.CtxOver Fp (Placed ProverEnvironment Fp))
    (point : Point (Witgen.FExprOver Fp (AssignedCell Fp))) :
    Witgen.eval ctx point = { x := Witgen.FExprOver.eval ctx point.x, y := Witgen.FExprOver.eval ctx point.y } := by
  with_unfolding_all rfl
end Halo2.Ironwood
