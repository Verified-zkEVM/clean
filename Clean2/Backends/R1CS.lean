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
variable {Native : Type} [Field Native]

structure LinComb (Native : Type) where
  const : Native
  terms : List (ℕ × Native)

namespace LinComb

def eval (env : ℕ → Native) (l : LinComb Native) : Native :=
  l.const + (l.terms.map fun t => t.2 * env t.1).sum

/-- The cells a linear combination mentions. -/
def footprint (l : LinComb Native) : Set ℕ := {c | c ∈ l.terms.map Prod.fst}

def cell (i : ℕ) : LinComb Native := ⟨0, [(i, 1)]⟩
def ofConst (c : Native) : LinComb Native := ⟨c, []⟩
def smul (c : Native) (l : LinComb Native) : LinComb Native := ⟨c * l.const, l.terms.map fun t => (t.1, c * t.2)⟩

instance : Add (LinComb Native) := ⟨fun a b => ⟨a.const + b.const, a.terms ++ b.terms⟩⟩
instance : Neg (LinComb Native) := ⟨smul (-1)⟩
instance : Sub (LinComb Native) := ⟨fun a b => a + -b⟩

variable {env : ℕ → Native}

theorem eval_frame (env env' : ℕ → Native) (l : LinComb Native) (h : ∀ c ∈ l.footprint, env c = env' c) :
    l.eval env = l.eval env' := by
  unfold eval
  congr 2
  apply List.map_congr_left
  intro t ht
  rw [h t.1 (List.mem_map.mpr ⟨t, ht, rfl⟩)]

@[circuit_norm] theorem eval_cell (i : ℕ) : (cell i : LinComb Native).eval env = env i := by
  simp [eval, cell]

@[circuit_norm] theorem eval_ofConst (c : Native) : (ofConst c).eval env = c := by
  simp [eval, ofConst]

@[circuit_norm] theorem eval_add (a b : LinComb Native) : (a + b).eval env = a.eval env + b.eval env := by
  show (⟨a.const + b.const, a.terms ++ b.terms⟩ : LinComb Native).eval env = _
  simp [eval]
  ring

@[circuit_norm] theorem eval_smul (c : Native) (l : LinComb Native) : (smul c l).eval env = c * l.eval env := by
  simp [eval, smul, Function.comp_def, mul_add, List.sum_map_mul_left, mul_assoc]

@[circuit_norm] theorem eval_neg (l : LinComb Native) : (-l).eval env = -l.eval env := by
  show (smul (-1) l).eval env = _
  simp [eval_smul]

@[circuit_norm] theorem eval_sub (a b : LinComb Native) : (a - b).eval env = a.eval env - b.eval env := by
  show (a + -b).eval env = _
  simp [eval_add, eval_neg, sub_eq_add_neg]

@[circuit_norm] theorem footprint_cell (i : ℕ) : (cell i : LinComb Native).footprint = {i} := by
  ext c; simp [footprint, cell]

omit [Field Native] in
@[circuit_norm] theorem footprint_ofConst (c : Native) : (ofConst c).footprint = ∅ := by
  ext c; simp [footprint, ofConst]

@[circuit_norm] theorem footprint_add (a b : LinComb Native) : (a + b).footprint = a.footprint ∪ b.footprint := by
  show (⟨a.const + b.const, a.terms ++ b.terms⟩ : LinComb Native).footprint = _
  ext c; simp [footprint]

@[circuit_norm] theorem footprint_smul (c : Native) (l : LinComb Native) : (smul c l).footprint = l.footprint := by
  ext x; simp [footprint, smul, List.map_map, Function.comp_def]

@[circuit_norm] theorem footprint_neg (l : LinComb Native) : (-l).footprint = l.footprint :=
  footprint_smul (-1) l

@[circuit_norm] theorem footprint_sub (a b : LinComb Native) : (a - b).footprint = a.footprint ∪ b.footprint := by
  show (a + -b).footprint = _
  rw [footprint_add, footprint_neg]

end LinComb

inductive R1CSOp (Native : Type) where
  | witness (m : ℕ) (vars : Vector (LinComb Native) m) (f : Vector Native m → Native)
  | constraint (a b c : LinComb Native)

namespace R1CSOp

def advance : R1CSOp Native → ℕ → ℕ
  | .witness .., s => s + 1
  | .constraint .., s => s

def reads : R1CSOp Native → Set ℕ
  | .witness _ vars _ => Linear.witnessReads LinComb.footprint vars
  | .constraint a b c => a.footprint ∪ b.footprint ∪ c.footprint

def writes : R1CSOp Native → ℕ → Set ℕ
  | .witness .., s => {s}
  | .constraint .., _ => ∅

def Holds (env : ℕ → Native) (_ : ℕ) : R1CSOp Native → Prop
  | .witness .. => True
  | .constraint a b c => a.eval env * b.eval env = c.eval env

def Honest (env : ℕ → Native) (s : ℕ) : R1CSOp Native → Prop
  | .witness _ vars f => Linear.WitnessHonest LinComb.eval env s vars f
  | .constraint .. => True

end R1CSOp

-- `implicit_reducible`: see `ExprBackend`
@[implicit_reducible]
def R1CS (Native : Type) [Field Native] : Backend where
  Native := Native
  Cell := ℕ
  Var := LinComb Native
  eval env l := l.eval env
  footprint := LinComb.footprint
  eval_frame := LinComb.eval_frame
  State := ℕ
  Alloc := Linear.Alloc
  Op := R1CSOp Native
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
instance : Field (R1CS Native).Native := ‹Field Native›
instance [DecidableEq Native] : DecidableEq (R1CS Native).Native := ‹DecidableEq Native›

namespace R1CS

@[circuit_norm] theorem eval_def (env : ℕ → Native) (l : LinComb Native) : (R1CS Native).eval env l = l.eval env := rfl
@[circuit_norm] theorem footprint_def (l : LinComb Native) : (R1CS Native).footprint l = l.footprint := rfl
@[circuit_norm] theorem alloc_def (s : ℕ) : (R1CS Native).Alloc s = Linear.Alloc s := rfl
@[circuit_norm] theorem advance_witness {m : ℕ} (vars : Vector (LinComb Native) m) (f : Vector Native m → Native) (s : ℕ) :
    (R1CS Native).advance (.witness m vars f) s = s + 1 := rfl
@[circuit_norm] theorem advance_constraint (a b c : LinComb Native) (s : ℕ) :
    (R1CS Native).advance (.constraint a b c) s = s := rfl
@[circuit_norm] theorem reads_witness {m : ℕ} (vars : Vector (LinComb Native) m) (f : Vector Native m → Native) :
    (R1CS Native).reads (.witness m vars f) = Linear.witnessReads LinComb.footprint vars := rfl
@[circuit_norm] theorem reads_constraint (a b c : LinComb Native) :
    (R1CS Native).reads (.constraint a b c) = a.footprint ∪ b.footprint ∪ c.footprint := rfl
@[circuit_norm] theorem holds_witness (env : ℕ → Native) (s : ℕ) {m : ℕ} (vars : Vector (LinComb Native) m) (f : Vector Native m → Native) :
    (R1CS Native).Holds env s (.witness m vars f) = True := rfl
@[circuit_norm] theorem holds_constraint (env : ℕ → Native) (s : ℕ) (a b c : LinComb Native) :
    (R1CS Native).Holds env s (.constraint a b c) = (a.eval env * b.eval env = c.eval env) := rfl
@[circuit_norm] theorem honest_witness (env : ℕ → Native) (s : ℕ) {m : ℕ} (vars : Vector (LinComb Native) m) (f : Vector Native m → Native) :
    (R1CS Native).Honest env s (.witness m vars f) = (env s = f (vars.map (LinComb.eval env))) := rfl
@[circuit_norm] theorem honest_constraint (env : ℕ → Native) (s : ℕ) (a b c : LinComb Native) :
    (R1CS Native).Honest env s (.constraint a b c) = True := rfl

@[circuit_norm]
def witness {m : ℕ} (vars : Vector (LinComb Native) m) (f : Vector Native m → Native) : Circuit (R1CS Native) (LinComb Native) :=
  fun s => (.cell s, [.native (.witness m vars f)])

@[circuit_norm]
def constraint (a b c : LinComb Native) : Circuit (R1CS Native) Unit :=
  Circuit.native (.constraint a b c)

/-! Native implementations: exactly `Base.interface`. Linear operations are free. -/

def add : Impl (R1CS Native) Add.interface where
  main | ((a, b) : LinComb Native × LinComb Native) => pure (a + b)
  spatial := by
    intro (a, b) s h
    simp_all [circuit_norm]
  soundness := by
    intro s env (a, b) _ _
    simp [circuit_norm]
  completeness := by
    intro s env (a, b) _ _
    simp [circuit_norm]

def sub : Impl (R1CS Native) Sub.interface where
  main | ((a, b) : LinComb Native × LinComb Native) => pure (a - b)
  spatial := by
    intro (a, b) s h
    simp_all [circuit_norm]
  soundness := by
    intro s env (a, b) _ _
    simp [circuit_norm]
  completeness := by
    intro s env (a, b) _ _
    simp [circuit_norm]

/-- One implementation for every scalar. -/
def scale (c : Native) : Impl (R1CS Native) (Scale.interface c) where
  main x := pure (LinComb.smul c x)
  spatial := by
    intro x s h
    simp_all [circuit_norm]
  soundness := by
    intro s env x _ _
    simp [circuit_norm]
  completeness := by
    intro s env x _ _
    simp [circuit_norm]

/-- One implementation for every constant. -/
def const (c : Native) : Impl (R1CS Native) (Const.interface c) where
  main _ := pure (LinComb.ofConst c)
  spatial := by
    intro _ s _
    simp [circuit_norm]
  soundness := by
    intro s env _ _ _
    simp [circuit_norm]
  completeness := by
    intro s env _ _ _
    simp [circuit_norm]

def mulEq : Impl (R1CS Native) MulEq.interface where
  main | (a, b, c) => constraint a b c
  spatial := by
    intro (a, b, c) s h
    simp_all [circuit_norm]
  soundness := by
    intro s env (a, b, c) _ h
    simp_all [circuit_norm]
  completeness := by
    intro s env (a, b, c) _ h
    simp_all [circuit_norm]

/-- One implementation for every witness computation, over any input shape. -/
def witnessImpl (p : Witness.Params Native) : Impl (R1CS Native) (Witness.interface p) where
  main input := witness (toElements input) fun v => p.f (fromElements v)
  spatial := by
    intro input s h
    simp only [circuit_norm]
    exact ⟨h, Linear.singleton_subset_alloc_succ s⟩
  soundness := by
    intro s env input _ _
    simp [circuit_norm]
  completeness := by
    intro s env input h _
    simp only [circuit_norm] at h ⊢
    rw [h, ProvableType.map_eq_fromElements]
    rfl

/-- What R1CS has natively. -/
def base : ∀ n, Impl (R1CS Native) (Base.interface n)
  | .add => add
  | .sub => sub
  | .scale c => scale c
  | .const c => const c
  | .mulEq => mulEq
  | @Base.Name.witness _ Input inst f => letI := inst; witnessImpl ⟨Input, f⟩

/-- The full arithmetic vocabulary, derived: `mul` costs a cell and a constraint. -/
def arith : ∀ n, Impl (R1CS Native) (Arith.interface n) := Arith.ofBase base

end R1CS
end Clean2
