import Clean.Circuit.WitnessIR

/-!
# Authoring sugar for the witness IR

Makes witness-IR programs read like normal code:

- typeclass operators on the IR expression types (`+ * - ⁻¹` on `FExpr`;
  `+ * / % &&& ||| ^^^ <<< >>>` on `NExpr`), numeric literals via `OfNat`,
  and a coercion from circuit `Expression`s,
- dot-notation bridges `x.val : NExpr` (on `Expression` and `FExpr`) and
  `n.toField : FExpr`,
- condition notation `=?` / `<?`,
- `VExpr.range n fun i => ...` — loop former whose body receives the index as an
  `NExpr` (applied to `.idx` at construction time, so the lambda is authoring-time
  only and the result is first-order data),
- a builder monad `Witgen.M` with `letF`/`letN` for shared intermediate values,
  assembled by `WitgenIR.build`.

Example (SHA256 `Add32`-style):
```
witnessVectorProgram 32 do
  let s ← (bitsVal a + bitsVal b) % ((2^32 : ℕ) : NExpr F)
  return .range 32 fun i => ((s >>> i) % 2).toField
```
-/

variable {F : Type} {α β : Type}

namespace Witgen

/-! ## Operators and coercions -/

instance : Coe (Expression F) (FExpr F) := ⟨.expr⟩
instance : Coe F (FExpr F) := ⟨.const⟩
instance {n : ℕ} [OfNat F n] : OfNat (FExpr F) n := ⟨.const (OfNat.ofNat n)⟩
instance : Add (FExpr F) := ⟨.add⟩
instance : Mul (FExpr F) := ⟨.mul⟩
instance : Inv (FExpr F) := ⟨.inv⟩
instance [Field F] : Neg (FExpr F) := ⟨.neg⟩
instance [Field F] : Sub (FExpr F) := ⟨.sub⟩

instance : Coe ℕ (NExpr F) := ⟨.const⟩
instance {n : ℕ} : OfNat (NExpr F) n := ⟨.const n⟩
instance : Add (NExpr F) := ⟨.add⟩
instance : Mul (NExpr F) := ⟨.mul⟩
instance : Div (NExpr F) := ⟨.div⟩
instance : Mod (NExpr F) := ⟨.mod⟩
instance : AndOp (NExpr F) := ⟨.land⟩
instance : OrOp (NExpr F) := ⟨.lor⟩
instance : XorOp (NExpr F) := ⟨.lxor⟩
instance : ShiftLeft (NExpr F) := ⟨.shiftL⟩
instance : ShiftRight (NExpr F) := ⟨.shiftR⟩

/-- A single field-sorted expression is a length-1 witness program, so scalar
sites can pass an `FExpr` to the generic `witness`. -/
instance : Coe (FExpr F) (WitgenIR F 1) := ⟨.ofFExpr⟩

/-! ## Bridges as dot notation -/

/-- The `ℕ` value of an IR field expression: `e.val`. -/
@[reducible] def FExpr.val (e : FExpr F) : NExpr F := .val e

/-- The `ℕ` value of a circuit expression, as a witness-IR expression: `x.val`. -/
@[reducible] def _root_.Expression.val (e : Expression F) : NExpr F := .val (.expr e)

/-- Cast a Nat-sorted IR expression back into the field (via `FiniteField.fromNat`). -/
@[reducible] def NExpr.toField (n : NExpr F) : FExpr F := .ofNat n

/-! ## Conditions -/

@[inherit_doc BExpr.feq] infix:50 " =? " => BExpr.feq
@[inherit_doc BExpr.lt] infix:50 " <? " => BExpr.lt

/-! ## Loop former -/

/-- Vector output built per index; the body receives the loop index as an `NExpr`.
The lambda is applied to `.idx` at construction time — authoring-time HOAS,
first-order result. -/
def VExpr.range (n : ℕ) (body : NExpr F → FExpr F) : VExpr F n :=
  .mapRange n (body .idx)

@[circuit_norm]
theorem VExpr.range_def (n : ℕ) (body : NExpr F → FExpr F) :
    VExpr.range n body = .mapRange n (body .idx) := rfl

/-! ## Builder monad for stepped programs -/

/-- Witness-program builder: accumulates `let`-steps, so shared values are written
in `do`-notation via `letF` / `letN`. -/
def M (F : Type) (α : Type) : Type :=
  Array (Step F) → α × Array (Step F)

instance : Monad (M F) where
  pure a := fun s => (a, s)
  bind m f := fun s => let (a, s') := m s; f a s'
  map f m := fun s => let (a, s') := m s; (f a, s')

attribute [circuit_norm] Array.size_empty Array.getElem?_push

@[circuit_norm]
theorem M.pure_def (a : α) :
    (pure a : M F α) = fun s => (a, s) := rfl

@[circuit_norm]
theorem M.bind_def (m : M F α) (f : α → M F β) :
    (m >>= f) = fun s => let (a, s') := m s; f a s' := rfl

@[circuit_norm]
theorem M.map_def (f : α → β) (m : M F α) :
    (f <$> m) = fun s => let (a, s') := m s; (f a, s') := rfl

/-- Bind a Nat-sorted value as a shared step; returns a reference to it. -/
def letN (e : NExpr F) : M F (NExpr F) :=
  fun s => (.localVar s.size, s.push (.letN e))

instance : CoeOut (NExpr F) (M F (NExpr F)) := ⟨letN⟩

@[circuit_norm]
theorem letN_def (e : NExpr F) :
    letN e = fun s => (.localVar s.size, s.push (.letN e)) := rfl

/-- Bind a field-sorted value as a shared step; returns a reference to it. -/
def letF (e : FExpr F) : M F (FExpr F) :=
  fun s => (.localVar s.size, s.push (.letF e))

instance : CoeOut (FExpr F) (M F (FExpr F)) := ⟨letF⟩

@[circuit_norm]
theorem letF_def (e : FExpr F) :
    letF e = fun s => (.localVar s.size, s.push (.letF e)) := rfl

/-- Assemble a witness program from a builder computation returning the output vector. -/
def WitgenIR.build {n : ℕ} (m : M F (VExpr F n)) : WitgenIR F n :=
  .ir (m #[]).2.toList (m #[]).1

@[circuit_norm]
theorem WitgenIR.build_def {n : ℕ} (m : M F (VExpr F n)) :
    WitgenIR.build m = .ir (m #[]).2.toList (m #[]).1 := rfl

end Witgen
