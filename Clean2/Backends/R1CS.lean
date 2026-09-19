/-
The R1CS backend: variables are linear combinations of cells, and the only constraint is
`a * b = c` on three linear combinations. Linear arithmetic is free; multiplication costs a
cell and a constraint.
-/
module

public import Clean2.Functionalities.Arith
public import Clean2.Backends.Linear
public import Mathlib.Algebra.BigOperators.Ring.List

@[expose] public section

namespace Clean2
variable {F : Type} [Field F]

structure LinComb (F : Type) where
  const : F
  terms : List (ℕ × F)

namespace LinComb

def eval (env : ℕ → F) (l : LinComb F) : F :=
  l.const + (l.terms.map fun t => t.2 * env t.1).sum

/-- The cells a linear combination mentions. -/
def footprint (l : LinComb F) : Set ℕ := {c | c ∈ l.terms.map Prod.fst}

def cell (i : ℕ) : LinComb F := ⟨0, [(i, 1)]⟩
def ofConst (c : F) : LinComb F := ⟨c, []⟩
def smul (c : F) (l : LinComb F) : LinComb F := ⟨c * l.const, l.terms.map fun t => (t.1, c * t.2)⟩

instance : Add (LinComb F) := ⟨fun a b => ⟨a.const + b.const, a.terms ++ b.terms⟩⟩
instance : Neg (LinComb F) := ⟨smul (-1)⟩
instance : Sub (LinComb F) := ⟨fun a b => a + -b⟩

variable {env : ℕ → F}

theorem eval_frame (env env' : ℕ → F) (l : LinComb F) (h : ∀ c ∈ l.footprint, env c = env' c) :
    l.eval env = l.eval env' := by
  unfold eval
  congr 2
  apply List.map_congr_left
  intro t ht
  rw [h t.1 (List.mem_map.mpr ⟨t, ht, rfl⟩)]

@[circuit_norm] theorem eval_cell (i : ℕ) : (cell i : LinComb F).eval env = env i := by
  simp [eval, cell]

@[circuit_norm] theorem eval_ofConst (c : F) : (ofConst c).eval env = c := by
  simp [eval, ofConst]

@[circuit_norm] theorem eval_add (a b : LinComb F) : (a + b).eval env = a.eval env + b.eval env := by
  show (⟨a.const + b.const, a.terms ++ b.terms⟩ : LinComb F).eval env = _
  simp [eval]
  ring

@[circuit_norm] theorem eval_smul (c : F) (l : LinComb F) : (smul c l).eval env = c * l.eval env := by
  simp [eval, smul, Function.comp_def, mul_add, List.sum_map_mul_left, mul_assoc]

@[circuit_norm] theorem eval_neg (l : LinComb F) : (-l).eval env = -l.eval env := by
  show (smul (-1) l).eval env = _
  simp [eval_smul]

@[circuit_norm] theorem eval_sub (a b : LinComb F) : (a - b).eval env = a.eval env - b.eval env := by
  show (a + -b).eval env = _
  simp [eval_add, eval_neg, sub_eq_add_neg]

@[circuit_norm] theorem footprint_cell (i : ℕ) : (cell i : LinComb F).footprint = {i} := by
  ext c; simp [footprint, cell]

omit [Field F] in
@[circuit_norm] theorem footprint_ofConst (c : F) : (ofConst c).footprint = ∅ := by
  ext c; simp [footprint, ofConst]

@[circuit_norm] theorem footprint_add (a b : LinComb F) : (a + b).footprint = a.footprint ∪ b.footprint := by
  show (⟨a.const + b.const, a.terms ++ b.terms⟩ : LinComb F).footprint = _
  ext c; simp [footprint]

@[circuit_norm] theorem footprint_smul (c : F) (l : LinComb F) : (smul c l).footprint = l.footprint := by
  ext x; simp [footprint, smul, List.map_map, Function.comp_def]

@[circuit_norm] theorem footprint_neg (l : LinComb F) : (-l).footprint = l.footprint :=
  footprint_smul (-1) l

@[circuit_norm] theorem footprint_sub (a b : LinComb F) : (a - b).footprint = a.footprint ∪ b.footprint := by
  show (a + -b).footprint = _
  rw [footprint_add, footprint_neg]

end LinComb

inductive R1CSOp (F : Type) where
  | witness (m : ℕ) (vars : Vector (LinComb F) m) (f : Vector F m → F)
  | constraint (a b c : LinComb F)

namespace R1CSOp

def advance : R1CSOp F → ℕ → ℕ
  | .witness .., s => s + 1
  | .constraint .., s => s

def reads : R1CSOp F → Set ℕ
  | .witness _ vars _ => Linear.witnessReads LinComb.footprint vars
  | .constraint a b c => a.footprint ∪ b.footprint ∪ c.footprint

def writes : R1CSOp F → ℕ → Set ℕ
  | .witness .., s => {s}
  | .constraint .., _ => ∅

def Holds (env : ℕ → F) (_ : ℕ) : R1CSOp F → Prop
  | .witness .. => True
  | .constraint a b c => a.eval env * b.eval env = c.eval env

def Honest (env : ℕ → F) (s : ℕ) : R1CSOp F → Prop
  | .witness _ vars f => Linear.WitnessHonest LinComb.eval env s vars f
  | .constraint .. => True

end R1CSOp

-- `implicit_reducible`: see `ExprBackend`
@[implicit_reducible]
def R1CS (F : Type) [Field F] : Backend where
  Native := F
  Cell := ℕ
  Var := LinComb F
  eval env l := l.eval env
  footprint := LinComb.footprint
  eval_frame := LinComb.eval_frame
  State := ℕ
  Alloc := Linear.Alloc
  Op := R1CSOp F
  advance := R1CSOp.advance
  alloc_mono op s := by cases op <;> first | exact Linear.alloc_mono_succ s | exact le_rfl
  reads := R1CSOp.reads
  writes := R1CSOp.writes
  writes_fresh op s := by
    cases op
    · exact ⟨Linear.disjoint_singleton_alloc s, Linear.singleton_subset_alloc_succ s⟩
    · exact ⟨disjoint_bot_left, Set.empty_subset _⟩
  Holds := R1CSOp.Holds
  Honest := R1CSOp.Honest
  honest_frame env env' s op h_reads h h_agree := by
    cases op
    · exact Linear.witnessHonest_frame LinComb.eval LinComb.footprint LinComb.eval_frame h_reads h h_agree
    · trivial
  honest_extend env₀ s op h_reads := by
    cases op
    · exact Linear.witnessHonest_extend LinComb.eval LinComb.footprint LinComb.eval_frame env₀ h_reads
    · exact ⟨env₀, fun _ _ => rfl, trivial⟩

/-- The native values of the R1CS backend are the field it is built over. -/
instance : Field (R1CS F).Native := ‹Field F›

namespace R1CS

@[circuit_norm] theorem eval_def (env : ℕ → F) (l : LinComb F) : (R1CS F).eval env l = l.eval env := rfl
@[circuit_norm] theorem footprint_def (l : LinComb F) : (R1CS F).footprint l = l.footprint := rfl
@[circuit_norm] theorem alloc_def (s : ℕ) : (R1CS F).Alloc s = Linear.Alloc s := rfl
@[circuit_norm] theorem advance_witness {m : ℕ} (vars : Vector (LinComb F) m) (f : Vector F m → F) (s : ℕ) :
    (R1CS F).advance (.witness m vars f) s = s + 1 := rfl
@[circuit_norm] theorem advance_constraint (a b c : LinComb F) (s : ℕ) :
    (R1CS F).advance (.constraint a b c) s = s := rfl
@[circuit_norm] theorem reads_witness {m : ℕ} (vars : Vector (LinComb F) m) (f : Vector F m → F) :
    (R1CS F).reads (.witness m vars f) = Linear.witnessReads LinComb.footprint vars := rfl
@[circuit_norm] theorem reads_constraint (a b c : LinComb F) :
    (R1CS F).reads (.constraint a b c) = a.footprint ∪ b.footprint ∪ c.footprint := rfl
@[circuit_norm] theorem holds_witness (env : ℕ → F) (s : ℕ) {m : ℕ} (vars : Vector (LinComb F) m) (f : Vector F m → F) :
    (R1CS F).Holds env s (.witness m vars f) = True := rfl
@[circuit_norm] theorem holds_constraint (env : ℕ → F) (s : ℕ) (a b c : LinComb F) :
    (R1CS F).Holds env s (.constraint a b c) = (a.eval env * b.eval env = c.eval env) := rfl
@[circuit_norm] theorem honest_witness (env : ℕ → F) (s : ℕ) {m : ℕ} (vars : Vector (LinComb F) m) (f : Vector F m → F) :
    (R1CS F).Honest env s (.witness m vars f) = (env s = f (vars.map (LinComb.eval env))) := rfl
@[circuit_norm] theorem honest_constraint (env : ℕ → F) (s : ℕ) (a b c : LinComb F) :
    (R1CS F).Honest env s (.constraint a b c) = True := rfl

@[circuit_norm]
def witness {m : ℕ} (vars : Vector (LinComb F) m) (f : Vector F m → F) : Circuit (R1CS F) (LinComb F) :=
  fun s => (.cell s, [.native (.witness m vars f)])

@[circuit_norm]
def constraint (a b c : LinComb F) : Circuit (R1CS F) Unit :=
  Circuit.native (.constraint a b c)

/-! Native implementations: exactly `Base.sig`. Linear operations are free. -/

def add : Impl (R1CS F) Add.iface where
  main := fun ((a, b) : LinComb F × LinComb F) => pure (a + b)
  spatial := by
    intro (a, b) s h
    simp_all [circuit_norm]
  soundness := by
    intro s env (a, b) _ _
    simp [circuit_norm, Add.iface]
  completeness := by
    intro s env (a, b) _ _
    simp [circuit_norm, Add.iface]

def sub : Impl (R1CS F) Sub.iface where
  main := fun ((a, b) : LinComb F × LinComb F) => pure (a - b)
  spatial := by
    intro (a, b) s h
    simp_all [circuit_norm]
  soundness := by
    intro s env (a, b) _ _
    simp [circuit_norm, Sub.iface]
  completeness := by
    intro s env (a, b) _ _
    simp [circuit_norm, Sub.iface]

def const (c : F) : Impl (R1CS F) (Const.iface c) where
  main _ := pure (LinComb.ofConst c)
  spatial := by
    intro _ s _
    simp [circuit_norm]
  soundness := by
    intro s env _ _ _
    simp [circuit_norm, Const.iface]
  completeness := by
    intro s env _ _ _
    simp [circuit_norm, Const.iface]

def mulEq : Impl (R1CS F) MulEq.iface where
  main | (a, b, c) => constraint a b c
  spatial := by
    intro (a, b, c) s h
    simp_all [circuit_norm]
  soundness := by
    intro s env (a, b, c) _ h
    simp_all [circuit_norm, MulEq.iface]
  completeness := by
    intro s env (a, b, c) _ h
    simp_all [circuit_norm, MulEq.iface]

def witnessImpl {Input : TypeMap} [ProvableType Input] (f : Input F → F) :
    Impl (R1CS F) (Witness.iface f) where
  main input := witness (toElements input) fun v => f (fromElements v)
  spatial := by
    intro input s h
    simp only [circuit_norm]
    exact ⟨h, Linear.singleton_subset_alloc_succ s⟩
  soundness := by
    intro s env input _ _
    simp [circuit_norm, Witness.iface]
  completeness := by
    intro s env input h _
    simp only [circuit_norm, Witness.iface] at h ⊢
    rw [h, ProvableType.map_eq_fromElements]
    rfl

/-- What R1CS has natively. -/
def base : Sig.Impl (R1CS F) Base.sig
  | .add => add
  | .sub => sub
  | .const c => const c
  | .mulEq => mulEq
  | @Base.Name.witness _ _Input inst f => letI := inst; witnessImpl f

/-- The full arithmetic signature, derived: `mul` costs a cell and a constraint. -/
def arith : Sig.Impl (R1CS F) Arith.sig := Arith.ofBase base

end R1CS
end Clean2
