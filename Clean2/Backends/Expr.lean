/-
The expression backend: variables are expression trees over cells, and the native
operations are `witness` (allocate a cell) and `assertZero` (an expression is zero).
This is the arithmetization of the old Clean core.
-/
module

public import Clean2.Functionalities.Arith
public import Clean2.Backends.Linear

@[expose] public section

namespace Clean2
variable {F : Type} [Field F]

inductive Expr (F : Type) where
  | var : ℕ → Expr F
  | const : F → Expr F
  | add : Expr F → Expr F → Expr F
  | mul : Expr F → Expr F → Expr F

namespace Expr

@[circuit_norm]
def eval (env : ℕ → F) : Expr F → F
  | var i => env i
  | const c => c
  | add a b => eval env a + eval env b
  | mul a b => eval env a * eval env b

@[circuit_norm]
def footprint : Expr F → Set ℕ
  | var i => {i}
  | const _ => ∅
  | add a b => footprint a ∪ footprint b
  | mul a b => footprint a ∪ footprint b

theorem eval_frame (env env' : ℕ → F) : ∀ (e : Expr F),
    (∀ c ∈ e.footprint, env c = env' c) → e.eval env = e.eval env'
  | var i, h => h i rfl
  | const _, _ => rfl
  | add a b, h => by
    simp only [eval, footprint] at h ⊢
    rw [eval_frame env env' a fun c hc => h c (Or.inl hc), eval_frame env env' b fun c hc => h c (Or.inr hc)]
  | mul a b, h => by
    simp only [eval, footprint] at h ⊢
    rw [eval_frame env env' a fun c hc => h c (Or.inl hc), eval_frame env env' b fun c hc => h c (Or.inr hc)]

end Expr

inductive ExprOp (F : Type) where
  | witness (m : ℕ) (vars : Vector (Expr F) m) (f : Vector F m → F)
  | assertZero (e : Expr F)

namespace ExprOp

def advance : ExprOp F → ℕ → ℕ
  | .witness .., s => s + 1
  | .assertZero _, s => s

def reads : ExprOp F → Set ℕ
  | .witness _ vars _ => Linear.witnessReads Expr.footprint vars
  | .assertZero e => e.footprint

def writes : ExprOp F → ℕ → Set ℕ
  | .witness .., s => {s}
  | .assertZero _, _ => ∅

def Holds (env : ℕ → F) (_ : ℕ) : ExprOp F → Prop
  | .witness .. => True
  | .assertZero e => e.eval env = 0

def Honest (env : ℕ → F) (s : ℕ) : ExprOp F → Prop
  | .witness _ vars f => Linear.WitnessHonest Expr.eval env s vars f
  | .assertZero _ => True

end ExprOp

-- `implicit_reducible`: `(ExprBackend F).Var` unfolds to `Expr F` when implicit arguments are
-- checked (so `simp` lemmas about the monad apply), but `simp` does not reduce the backend's
-- projections into raw fields (so the lemmas below about them apply)
@[implicit_reducible]
def ExprBackend (F : Type) [Field F] : Backend where
  Native := F
  Cell := ℕ
  Var := Expr F
  eval env e := e.eval env
  footprint := Expr.footprint
  eval_frame := Expr.eval_frame
  State := ℕ
  Alloc := Linear.Alloc
  Op := ExprOp F
  advance := ExprOp.advance
  alloc_mono op s := by cases op <;> first | exact Linear.alloc_mono_succ s | exact le_rfl
  reads := ExprOp.reads
  writes := ExprOp.writes
  writes_fresh op s := by
    cases op
    · exact ⟨Linear.disjoint_singleton_alloc s, Linear.singleton_subset_alloc_succ s⟩
    · exact ⟨disjoint_bot_left, Set.empty_subset _⟩
  Holds := ExprOp.Holds
  Honest := ExprOp.Honest
  honest_frame env env' s op h_reads h h_agree := by
    cases op
    · exact Linear.witnessHonest_frame Expr.eval Expr.footprint Expr.eval_frame h_reads h h_agree
    · trivial
  honest_extend env₀ s op h_reads := by
    cases op
    · exact Linear.witnessHonest_extend Expr.eval Expr.footprint Expr.eval_frame env₀ h_reads
    · exact ⟨env₀, fun _ _ => rfl, trivial⟩

/-- The native values of the expression backend are the field it is built over. -/
instance : Field (ExprBackend F).Native := ‹Field F›

namespace ExprBackend

/-! The backend's definition, as simp lemmas. -/
@[circuit_norm] theorem eval_def (env : ℕ → F) (e : Expr F) : (ExprBackend F).eval env e = e.eval env := rfl
@[circuit_norm] theorem footprint_def (e : Expr F) : (ExprBackend F).footprint e = e.footprint := rfl
@[circuit_norm] theorem alloc_def (s : ℕ) : (ExprBackend F).Alloc s = Linear.Alloc s := rfl
@[circuit_norm] theorem advance_witness {m : ℕ} (vars : Vector (Expr F) m) (f : Vector F m → F) (s : ℕ) :
    (ExprBackend F).advance (.witness m vars f) s = s + 1 := rfl
@[circuit_norm] theorem advance_assertZero (e : Expr F) (s : ℕ) :
    (ExprBackend F).advance (.assertZero e) s = s := rfl
@[circuit_norm] theorem reads_witness {m : ℕ} (vars : Vector (Expr F) m) (f : Vector F m → F) :
    (ExprBackend F).reads (.witness m vars f) = Linear.witnessReads Expr.footprint vars := rfl
@[circuit_norm] theorem reads_assertZero (e : Expr F) :
    (ExprBackend F).reads (.assertZero e) = e.footprint := rfl
@[circuit_norm] theorem holds_witness (env : ℕ → F) (s : ℕ) {m : ℕ} (vars : Vector (Expr F) m) (f : Vector F m → F) :
    (ExprBackend F).Holds env s (.witness m vars f) = True := rfl
@[circuit_norm] theorem holds_assertZero (env : ℕ → F) (s : ℕ) (e : Expr F) :
    (ExprBackend F).Holds env s (.assertZero e) = (e.eval env = 0) := rfl
@[circuit_norm] theorem honest_witness (env : ℕ → F) (s : ℕ) {m : ℕ} (vars : Vector (Expr F) m) (f : Vector F m → F) :
    (ExprBackend F).Honest env s (.witness m vars f) = (env s = f (vars.map (Expr.eval env))) := rfl
@[circuit_norm] theorem honest_assertZero (env : ℕ → F) (s : ℕ) (e : Expr F) :
    (ExprBackend F).Honest env s (.assertZero e) = True := rfl

/-! Smart constructors for the native operations. -/

@[circuit_norm]
def witness {m : ℕ} (vars : Vector (Expr F) m) (f : Vector F m → F) : Circuit (ExprBackend F) (Expr F) :=
  fun s => (.var s, [.native (.witness m vars f)])

@[circuit_norm]
def assertZero (e : Expr F) : Circuit (ExprBackend F) Unit :=
  Circuit.native (.assertZero e)

/-! Native implementations of the arithmetic functionalities. Arithmetic is free: it just
builds a bigger expression. -/

def add : Impl (ExprBackend F) Add.interface where
  main | (a, b) => pure (Expr.add a b)
  spatial := by
    intro (a, b) s h
    simp_all [circuit_norm]
  soundness := by
    intro s env (a, b) _ _
    simp [circuit_norm, Add.interface]
  completeness := by
    intro s env (a, b) _ _
    simp [circuit_norm, Add.interface]

def sub : Impl (ExprBackend F) Sub.interface where
  main | (a, b) => pure (Expr.add a (Expr.mul (Expr.const (-1)) b))
  spatial := by
    intro (a, b) s h
    simp_all [circuit_norm]
  soundness := by
    intro s env (a, b) _ _
    simp [circuit_norm, Sub.interface, sub_eq_add_neg]
  completeness := by
    intro s env (a, b) _ _
    simp [circuit_norm, Sub.interface]

def mul : Impl (ExprBackend F) Mul.interface where
  main | (a, b) => pure (Expr.mul a b)
  spatial := by
    intro (a, b) s h
    simp_all [circuit_norm]
  soundness := by
    intro s env (a, b) _ _
    simp [circuit_norm, Mul.interface]
  completeness := by
    intro s env (a, b) _ _
    simp [circuit_norm, Mul.interface]

def const (c : F) : Impl (ExprBackend F) (Const.interface c) where
  main _ := pure (Expr.const c)
  spatial := by
    intro _ s _
    simp [circuit_norm]
  soundness := by
    intro s env _ _ _
    simp [circuit_norm, Const.interface]
  completeness := by
    intro s env _ _ _
    simp [circuit_norm, Const.interface]

def assertZeroImpl : Impl (ExprBackend F) AssertZero.interface where
  main e := assertZero e
  spatial := by
    intro e s h
    simp_all [circuit_norm]
  soundness := by
    intro s env e _ h
    simp_all [circuit_norm, AssertZero.interface]
  completeness := by
    intro s env e _ h
    simp_all [circuit_norm, AssertZero.interface]

def mulEq : Impl (ExprBackend F) MulEq.interface where
  main | (a, b, c) => assertZero (Expr.add (Expr.mul a b) (Expr.mul (Expr.const (-1)) c))
  spatial := by
    intro (a, b, c) s h
    simp_all [circuit_norm]
  soundness := by
    intro s env (a, b, c) _ h
    simp_all [circuit_norm, MulEq.interface]
    linear_combination h
  completeness := by
    intro s env (a, b, c) _ h
    simp_all [circuit_norm, MulEq.interface]

def witnessImpl {Input : TypeMap} [ProvableType Input] (f : Input F → F) :
    Impl (ExprBackend F) (Witness.interface f) where
  main input := witness (toElements input) fun v => f (fromElements v)
  spatial := by
    intro input s h
    simp only [circuit_norm]
    exact ⟨h, Linear.singleton_subset_alloc_succ s⟩
  soundness := by
    intro s env input _ _
    simp [circuit_norm, Witness.interface]
  completeness := by
    intro s env input h _
    simp only [circuit_norm, Witness.interface] at h ⊢
    rw [h, ProvableType.map_eq_fromElements]
    rfl

/-- The expression backend implements all of `Arith.sig` natively. -/
def arith : Sig.Impl (ExprBackend F) Arith.sig
  | .add => add
  | .sub => sub
  | .mul => mul
  | .const c => const c
  | .mulEq => mulEq
  | .assertZero => assertZeroImpl
  | @Arith.Name.witness _ _Input inst f => letI := inst; witnessImpl f

end ExprBackend
end Clean2
