module

public import Clean.Circuit.Lookup
public import Clean.Utils.Tactics.ProvableStructDeriving

@[expose] public section

namespace TestWitgenEvalProjection

-- A handwritten instance exercises the literal simproc's non-ProvableStruct path.
-- No `import all` should be needed to map its vector of field elements.
structure FlatRow (F : Type) where
  first : F
  second : F

instance : ProvableType FlatRow where
  size := 2
  toElements x := #v[x.first, x.second]
  fromElements v := ⟨v[0], v[1]⟩

example {F : Type} [FiniteField F] (ctx : Witgen.Ctx F) (a b : Witgen.FExpr F) :
    Witgen.eval ctx (FlatRow.mk a b) =
      FlatRow.mk (Witgen.FExpr.eval ctx a) (Witgen.FExpr.eval ctx b) := by
  simp only [circuit_norm]

structure TestRow (F : Type) where
  first : F
  second : F
deriving ProvableStruct

example {F : Type} [FiniteField F] (ctx : Witgen.Ctx F) (row : TestRow (Witgen.FExpr F)) :
    Witgen.FExpr.eval ctx row.first = (Witgen.eval ctx row).first := by
  simp [circuit_norm]

example {F : Type} [FiniteField F] (ctx : Witgen.Ctx F) (row : TestRow (Witgen.FExpr F)) :
    Witgen.FExpr.eval ctx row.second = (Witgen.eval ctx row).second := by
  simp [circuit_norm]

def TestTable (F : Type) : Table F TestRow where
  name := "test"
  Contains _ _ := True

example {F : Type} [FiniteField F] (ctx : Witgen.Ctx F) (row : Witgen.U64Expr F) :
    Witgen.FExpr.eval ctx ((TestTable F).dataGet row).second =
      (((ctx.env.data.getTable (TestTable F))[(row.eval ctx).toNat]?.getD default).second) := by
  simp [circuit_norm]

example {F : Type} [FiniteField F] (ctx : Witgen.Ctx F) (row : Witgen.U64Expr F) :
    Witgen.FExpr.eval ctx ((TestTable F).hintGet row).second =
      ((fromElements (((ctx.env.hint (TestTable F).name (size TestRow))[(row.eval ctx).toNat]?).getD default)
        : TestRow F).second) := by
  simp [circuit_norm]

end TestWitgenEvalProjection
