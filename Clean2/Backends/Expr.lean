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
variable {Native : Type} [Field Native]

inductive Expr (Native : Type) where
  | var : ℕ → Expr Native
  | const : Native → Expr Native
  | add : Expr Native → Expr Native → Expr Native
  | mul : Expr Native → Expr Native → Expr Native

namespace Expr

@[circuit_norm]
def eval (env : ℕ → Native) : Expr Native → Native
  | var i => env i
  | const c => c
  | add a b => eval env a + eval env b
  | mul a b => eval env a * eval env b

@[circuit_norm]
def footprint : Expr Native → Set ℕ
  | var i => {i}
  | const _ => ∅
  | add a b => footprint a ∪ footprint b
  | mul a b => footprint a ∪ footprint b

theorem eval_frame (env env' : ℕ → Native) : ∀ (e : Expr Native),
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

inductive ExprOp (Native : Type) where
  | witness (m : ℕ) (vars : Vector (Expr Native) m) (f : Vector Native m → Native)
  | assertZero (e : Expr Native)

namespace ExprOp

def advance : ExprOp Native → ℕ → ℕ
  | .witness .., s => s + 1
  | .assertZero _, s => s

def reads : ExprOp Native → Set ℕ
  | .witness _ vars _ => Linear.witnessReads Expr.footprint vars
  | .assertZero e => e.footprint

def writes : ExprOp Native → ℕ → Set ℕ
  | .witness .., s => {s}
  | .assertZero _, _ => ∅

def Holds (env : ℕ → Native) (_ : ℕ) : ExprOp Native → Prop
  | .witness .. => True
  | .assertZero e => e.eval env = 0

def Honest (env : ℕ → Native) (s : ℕ) : ExprOp Native → Prop
  | .witness _ vars f => Linear.WitnessHonest Expr.eval env s vars f
  | .assertZero _ => True

end ExprOp

-- `implicit_reducible`: `(ExprBackend Native).Var` unfolds to `Expr Native` when implicit arguments are
-- checked (so `simp` lemmas about the monad apply), but `simp` does not reduce the backend's
-- projections into raw fields (so the lemmas below about them apply)
@[implicit_reducible]
def ExprBackend (Native : Type) [Field Native] : Backend where
  Native := Native
  Cell := ℕ
  Var := Expr Native
  eval env e := e.eval env
  footprint := Expr.footprint
  eval_frame := Expr.eval_frame
  State := ℕ
  Alloc := Linear.Alloc
  Op := ExprOp Native
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
instance : Field (ExprBackend Native).Native := ‹Field Native›

namespace ExprBackend

/-! The backend's definition, as simp lemmas. -/
@[circuit_norm] theorem eval_def (env : ℕ → Native) (e : Expr Native) : (ExprBackend Native).eval env e = e.eval env := rfl
@[circuit_norm] theorem footprint_def (e : Expr Native) : (ExprBackend Native).footprint e = e.footprint := rfl
@[circuit_norm] theorem alloc_def (s : ℕ) : (ExprBackend Native).Alloc s = Linear.Alloc s := rfl
@[circuit_norm] theorem advance_witness {m : ℕ} (vars : Vector (Expr Native) m) (f : Vector Native m → Native) (s : ℕ) :
    (ExprBackend Native).advance (.witness m vars f) s = s + 1 := rfl
@[circuit_norm] theorem advance_assertZero (e : Expr Native) (s : ℕ) :
    (ExprBackend Native).advance (.assertZero e) s = s := rfl
@[circuit_norm] theorem reads_witness {m : ℕ} (vars : Vector (Expr Native) m) (f : Vector Native m → Native) :
    (ExprBackend Native).reads (.witness m vars f) = Linear.witnessReads Expr.footprint vars := rfl
@[circuit_norm] theorem reads_assertZero (e : Expr Native) :
    (ExprBackend Native).reads (.assertZero e) = e.footprint := rfl
@[circuit_norm] theorem holds_witness (env : ℕ → Native) (s : ℕ) {m : ℕ} (vars : Vector (Expr Native) m) (f : Vector Native m → Native) :
    (ExprBackend Native).Holds env s (.witness m vars f) = True := rfl
@[circuit_norm] theorem holds_assertZero (env : ℕ → Native) (s : ℕ) (e : Expr Native) :
    (ExprBackend Native).Holds env s (.assertZero e) = (e.eval env = 0) := rfl
@[circuit_norm] theorem honest_witness (env : ℕ → Native) (s : ℕ) {m : ℕ} (vars : Vector (Expr Native) m) (f : Vector Native m → Native) :
    (ExprBackend Native).Honest env s (.witness m vars f) = (env s = f (vars.map (Expr.eval env))) := rfl
@[circuit_norm] theorem honest_assertZero (env : ℕ → Native) (s : ℕ) (e : Expr Native) :
    (ExprBackend Native).Honest env s (.assertZero e) = True := rfl

/-! Smart constructors for the native operations. -/

@[circuit_norm]
def witness {m : ℕ} (vars : Vector (Expr Native) m) (f : Vector Native m → Native) : Circuit (ExprBackend Native) (Expr Native) :=
  fun s => (.var s, [.native (.witness m vars f)])

@[circuit_norm]
def assertZero (e : Expr Native) : Circuit (ExprBackend Native) Unit :=
  Circuit.native (.assertZero e)

/-! Native implementations of the arithmetic functionalities. Arithmetic is free: it just
builds a bigger expression. -/

def add : Impl (ExprBackend Native) Add.interface where
  main | _, (a, b) => pure (Expr.add a b)
  spatial := by
    intro _ (a, b) s h
    simp_all [circuit_norm]
  soundness := by
    intro _ s env (a, b) _ _
    simp [circuit_norm]
  completeness := by
    intro _ s env (a, b) _ _
    simp [circuit_norm]

def sub : Impl (ExprBackend Native) Sub.interface where
  main | _, (a, b) => pure (Expr.add a (Expr.mul (Expr.const (-1)) b))
  spatial := by
    intro _ (a, b) s h
    simp_all [circuit_norm]
  soundness := by
    intro _ s env (a, b) _ _
    simp [circuit_norm, sub_eq_add_neg]
  completeness := by
    intro _ s env (a, b) _ _
    simp [circuit_norm]

def mul : Impl (ExprBackend Native) Mul.interface where
  main | _, (a, b) => pure (Expr.mul a b)
  spatial := by
    intro _ (a, b) s h
    simp_all [circuit_norm]
  soundness := by
    intro _ s env (a, b) _ _
    simp [circuit_norm]
  completeness := by
    intro _ s env (a, b) _ _
    simp [circuit_norm]

/-- One implementation for every scalar. -/
def scale : Impl (ExprBackend Native) Scale.interface where
  main c x := pure (Expr.mul (Expr.const c) x)
  spatial := by
    intro _ x s h
    simp_all [circuit_norm]
  soundness := by
    intro c s env x _ _
    simp [circuit_norm]
  completeness := by
    intro c s env x _ _
    simp [circuit_norm]

/-- One implementation for every constant. -/
def const : Impl (ExprBackend Native) Const.interface where
  main c _ := pure (Expr.const c)
  spatial := by
    intro _ _ s _
    simp [circuit_norm]
  soundness := by
    intro c s env _ _ _
    simp [circuit_norm]
  completeness := by
    intro c s env _ _ _
    simp [circuit_norm]

def assertZeroImpl : Impl (ExprBackend Native) AssertZero.interface where
  main _ e := assertZero e
  spatial := by
    intro _ e s h
    simp_all [circuit_norm]
  soundness := by
    intro _ s env e _ h
    simp_all [circuit_norm]
  completeness := by
    intro _ s env e _ h
    simp_all [circuit_norm]

def mulEq : Impl (ExprBackend Native) MulEq.interface where
  main | _, (a, b, c) => assertZero (Expr.add (Expr.mul a b) (Expr.mul (Expr.const (-1)) c))
  spatial := by
    intro _ (a, b, c) s h
    simp_all [circuit_norm]
  soundness := by
    intro _ s env (a, b, c) _ h
    simp_all [circuit_norm]
    linear_combination h
  completeness := by
    intro _ s env (a, b, c) _ h
    simp_all [circuit_norm]

/-- One implementation for every witness computation, over any input shape. -/
def witnessImpl : Impl (ExprBackend Native) Witness.interface where
  main p input := witness (toElements input) fun v => p.f (fromElements v)
  spatial := by
    intro _ input s h
    simp only [circuit_norm]
    exact ⟨h, Linear.singleton_subset_alloc_succ s⟩
  soundness := by
    intro _ s env input _ _
    simp [circuit_norm]
  completeness := by
    intro _ s env input h _
    simp only [circuit_norm] at h ⊢
    rw [h, ProvableType.map_eq_fromElements]
    rfl

/-- The expression backend implements all of `Arith.interface` natively. -/
def arith : Impl (ExprBackend Native) Arith.interface :=
  Impl.ofFun fun
  | .add => add
  | .sub => sub
  | .mul => mul
  | .scale c => scale.fix c
  | .const c => const.fix c
  | .mulEq => mulEq
  | .assertZero => assertZeroImpl
  | @Arith.Name.witness _ Input inst f => letI := inst; witnessImpl.fix ⟨Input, f⟩

end ExprBackend
end Clean2
