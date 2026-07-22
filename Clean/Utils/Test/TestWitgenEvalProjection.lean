import Clean.Circuit.Lookup
import Clean.Utils.Tactics.ProvableStructDeriving

open Clean

namespace TestWitgenEvalProjection

structure TestRow (F : Type) where
  first : F
  second : F
deriving ProvableStruct

example {F : Type} [FiniteField F] (ctx : Ctx F) (row : TestRow (FExpr F)) :
    Witgen.FExprOver.eval ctx row.first = (Witgen.eval ctx row).first := by
  simp [circuit_norm]

example {F : Type} [FiniteField F] (ctx : Ctx F) (row : TestRow (FExpr F)) :
    Witgen.FExprOver.eval ctx row.second = (Witgen.eval ctx row).second := by
  simp [circuit_norm]

def TestTable (F : Type) : Table F TestRow where
  name := "test"
  Contains _ _ := True

example {F : Type} [FiniteField F] (ctx : Ctx F) (row : NExpr F) :
    Witgen.FExprOver.eval ctx ((TestTable F).dataGet row).second =
      (((ctx.env.data.getTable (TestTable F))[row.eval ctx]?.getD default).second) := by
  simp [circuit_norm]

example {F : Type} [FiniteField F] (ctx : Ctx F) (row : NExpr F) :
    Witgen.FExprOver.eval ctx ((TestTable F).hintGet row).second =
      ((fromElements (((ctx.env.hint (TestTable F).name (size TestRow))[row.eval ctx]?).getD default)
        : TestRow F).second) := by
  simp [circuit_norm]

end TestWitgenEvalProjection
