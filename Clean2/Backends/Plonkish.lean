/-
The plonkish backend: a trace of rows and columns, and custom gates.

A cell is a (row, column) pair, a variable is a cell, and the native operation is *placing a
gate*. A gate is a set of polynomial identities over the cells of one row: some of them are
copied in from elsewhere (the inputs, through the permutation argument), some are set at
placement time (the fixed cells), and the rest the honest prover computes (the outputs).
Placing a gate allocates a row.

Gates are values carried by the operations, not a parameter of the backend: the
*configuration* of a circuit (the list of distinct gates it uses, what Halo2's `configure`
declares) is read off its operations (`Plonkish.config`). A gate is identified by its shape
(arities and polynomials), which is what the verifying key depends on; its witness computation
is not part of the identity.

Nothing is free here: `add` is a gate and costs a row. What the backend has natively is every
gate at every assignment of its fixed cells (`Plonkish.gate`), an interface indexed by the
fixed values, whose members are the polynomial identities themselves. A semantic contract
(`Poseidon.Round.interface`, `Add.interface`, ...) is obtained by refining it, which is a proof
about polynomials and never about circuits.
-/
module

public import Clean2.Functionalities.Arith
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn

@[expose] public section

namespace Clean2
variable {F : Type} [Field F]

/-! ## Gates -/

/-- A polynomial over the cells of a row: the inputs, the fixed cells, and the outputs. -/
inductive GateExpr (F : Type) (nIn nFixed nOut : ℕ) where
  | input (i : Fin nIn)
  | fixed (j : Fin nFixed)
  | output (o : Fin nOut)
  | const (c : F)
  | add (a b : GateExpr F nIn nFixed nOut)
  | mul (a b : GateExpr F nIn nFixed nOut)
  | neg (a : GateExpr F nIn nFixed nOut)
  | pow (a : GateExpr F nIn nFixed nOut) (k : ℕ)
  deriving DecidableEq

namespace GateExpr
variable {nIn nFixed nOut : ℕ}

instance : Add (GateExpr F nIn nFixed nOut) := ⟨add⟩
instance : Mul (GateExpr F nIn nFixed nOut) := ⟨mul⟩
instance : Neg (GateExpr F nIn nFixed nOut) := ⟨neg⟩
instance : Sub (GateExpr F nIn nFixed nOut) := ⟨fun a b => add a (neg b)⟩
instance : HPow (GateExpr F nIn nFixed nOut) ℕ (GateExpr F nIn nFixed nOut) := ⟨pow⟩

/-- The sum of a list of polynomials. -/
def sum : List (GateExpr F nIn nFixed nOut) → GateExpr F nIn nFixed nOut
  | [] => const 0
  | e :: es => e + sum es

@[circuit_norm]
def eval (x : Vector F nIn) (k : Vector F nFixed) (y : Vector F nOut) : GateExpr F nIn nFixed nOut → F
  | input i => x[i]
  | fixed j => k[j]
  | output o => y[o]
  | const c => c
  | add a b => a.eval x k y + b.eval x k y
  | mul a b => a.eval x k y * b.eval x k y
  | neg a => -a.eval x k y
  | pow a n => a.eval x k y ^ n

variable {x : Vector F nIn} {k : Vector F nFixed} {y : Vector F nOut}

@[circuit_norm] theorem eval_hadd (a b : GateExpr F nIn nFixed nOut) :
    (a + b).eval x k y = a.eval x k y + b.eval x k y := rfl
@[circuit_norm] theorem eval_hmul (a b : GateExpr F nIn nFixed nOut) :
    (a * b).eval x k y = a.eval x k y * b.eval x k y := rfl
@[circuit_norm] theorem eval_hneg (a : GateExpr F nIn nFixed nOut) : (-a).eval x k y = -a.eval x k y := rfl
@[circuit_norm] theorem eval_hsub (a b : GateExpr F nIn nFixed nOut) :
    (a - b).eval x k y = a.eval x k y - b.eval x k y := (sub_eq_add_neg _ _).symm
@[circuit_norm] theorem eval_hpow (a : GateExpr F nIn nFixed nOut) (n : ℕ) :
    (a ^ n).eval x k y = a.eval x k y ^ n := rfl

@[circuit_norm] theorem eval_sum (es : List (GateExpr F nIn nFixed nOut)) :
    (sum es).eval x k y = (es.map (eval x k y)).sum := by
  induction es with
  | nil => simp [sum, eval]
  | cons e es ih => simp [sum, eval_hadd, ih]

@[circuit_norm] theorem eval_sum_ofFn {m : ℕ} (f : Fin m → GateExpr F nIn nFixed nOut) :
    (sum (List.ofFn f)).eval x k y = ∑ i, (f i).eval x k y := by
  rw [eval_sum, List.map_ofFn, List.sum_ofFn]
  rfl

end GateExpr

/-- The shape of a gate: what the verifying key depends on. -/
structure GateShape (F : Type) where
  nIn : ℕ
  nFixed : ℕ
  nOut : ℕ
  polys : List (GateExpr F nIn nFixed nOut)
  deriving DecidableEq

/-- A gate: a shape, and how the honest prover fills the outputs from the inputs and the fixed
cells. -/
structure Gate (F : Type) extends GateShape F where
  witness : Vector F nIn → Vector F nFixed → Vector F nOut

namespace Gate

/-- Every identity of the gate holds on the row. -/
def Constraint (g : Gate F) (x : Vector F g.nIn) (k : Vector F g.nFixed) (y : Vector F g.nOut) : Prop :=
  ∀ e ∈ g.polys, e.eval x k y = 0

/-- The member of a gate at fixed values `k`: the verifier learns the identities, the honest
prover computes the outputs. A gate is a witness and an assertion fused into one row. Reducible,
like every interface. -/
@[reducible]
def member (g : Gate F) (k : Vector F g.nFixed) : Interface F where
  input := Vector F g.nIn
  inputCType := .natives g.nIn
  output := Vector F g.nOut
  outputCType := .natives g.nOut
  Spec x y := g.Constraint x k y
  ProverAssumptions x := g.Constraint x k (g.witness x k)
  ProverSpec x y := y = g.witness x k

end Gate

/-! ## The backend -/

/-- The native operation: place gate `g` on a fresh row, with its inputs copied from `inputs`
and its fixed cells set to `fixed`. -/
inductive PlonkishOp (F : Type) where
  | gate (g : Gate F) (inputs : Vector (ℕ × ℕ) g.nIn) (fixed : Vector F g.nFixed)

namespace Plonkish

/-- The cells allocated at state `s`: every cell of the rows below `s`. -/
def Alloc (s : ℕ) : Set (ℕ × ℕ) := {c | c.1 < s}

@[circuit_norm] theorem mem_alloc {c : ℕ × ℕ} {s : ℕ} : c ∈ Alloc s ↔ c.1 < s := Iff.rfl

theorem alloc_mono_succ (s : ℕ) : Alloc s ⊆ Alloc (s + 1) := fun _ hc => Nat.lt_succ_of_lt hc

/-- The row layout of a gate placed at row `s`: the inputs in the first columns, the outputs after. -/
def inCells (g : Gate F) (s : ℕ) : Vector (ℕ × ℕ) g.nIn := Vector.ofFn fun i => (s, i)
def outCells (g : Gate F) (s : ℕ) : Vector (ℕ × ℕ) g.nOut := Vector.ofFn fun o => (s, g.nIn + o)

/-- The cells an operation reads: its inputs. -/
def reads : PlonkishOp F → Set (ℕ × ℕ)
  | .gate g inputs _ => ⋃ i : Fin g.nIn, {inputs[i]}

/-- The cells an operation writes: the row it is placed on. -/
def writes : PlonkishOp F → ℕ → Set (ℕ × ℕ)
  | .gate g .., s => {c | c.1 = s ∧ c.2 < g.nIn + g.nOut}

/-- The inputs are copied into the row (the permutation argument), and the identities hold on
the row (the gate polynomials, enabled by the selector at this row). -/
def Holds (env : ℕ × ℕ → F) (s : ℕ) : PlonkishOp F → Prop
  | .gate g inputs k =>
    (inCells g s).map env = inputs.map env ∧
    g.Constraint ((inCells g s).map env) k ((outCells g s).map env)

/-- The honest prover copies the inputs and computes the outputs. -/
def Honest (env : ℕ × ℕ → F) (s : ℕ) : PlonkishOp F → Prop
  | .gate g inputs k =>
    (inCells g s).map env = inputs.map env ∧
    (outCells g s).map env = g.witness ((inCells g s).map env) k

omit [Field F] in
theorem map_congr_of_agree {m : ℕ} (v : Vector (ℕ × ℕ) m) {S : Set (ℕ × ℕ)} (hv : ∀ i : Fin m, v[i] ∈ S)
    {env env' : ℕ × ℕ → F} (h : ∀ c ∈ S, env c = env' c) : v.map env = v.map env' := by
  ext i hi
  simp only [Vector.getElem_map]
  exact h _ (hv ⟨i, hi⟩)

omit [Field F] in
theorem inCells_mem (g : Gate F) (s : ℕ) (i : Fin g.nIn) : (inCells g s)[i] ∈ Alloc (s + 1) := by
  simp [inCells, Alloc]

omit [Field F] in
theorem outCells_mem (g : Gate F) (s : ℕ) (o : Fin g.nOut) : (outCells g s)[o] ∈ Alloc (s + 1) := by
  simp [outCells, Alloc]

omit [Field F] in
theorem honest_frame (env env' : ℕ × ℕ → F) (s : ℕ) (op : PlonkishOp F) (h_reads : reads op ⊆ Alloc s)
    (h : Honest env s op) (h_agree : ∀ c ∈ Alloc (s + 1), env c = env' c) : Honest env' s op := by
  obtain ⟨g, inputs, k⟩ := op
  have h_inputs : ∀ i : Fin g.nIn, inputs[i] ∈ Alloc (s + 1) := fun i =>
    alloc_mono_succ s (h_reads (Set.mem_iUnion.mpr ⟨i, rfl⟩))
  simp only [Honest] at h ⊢
  rw [← map_congr_of_agree _ (inCells_mem g s) h_agree, ← map_congr_of_agree _ h_inputs h_agree,
    ← map_congr_of_agree _ (outCells_mem g s) h_agree]
  exact h

/-- The honest row on top of `env₀`: the inputs copied, the outputs computed. -/
def honestRow (env₀ : ℕ × ℕ → F) (s : ℕ) (g : Gate F) (inputs : Vector (ℕ × ℕ) g.nIn) (k : Vector F g.nFixed)
    (c : ℕ × ℕ) : F :=
  if c.1 = s then
    if h : c.2 < g.nIn then env₀ inputs[c.2]
    else if h' : c.2 - g.nIn < g.nOut then (g.witness (inputs.map env₀) k)[c.2 - g.nIn]
    else env₀ c
  else env₀ c

omit [Field F] in
theorem honest_extend (env₀ : ℕ × ℕ → F) (s : ℕ) (op : PlonkishOp F) (h_reads : reads op ⊆ Alloc s) :
    ∃ env, (∀ c ∈ Alloc s, env c = env₀ c) ∧ Honest env s op := by
  obtain ⟨g, inputs, k⟩ := op
  have h_inputs : ∀ i : Fin g.nIn, inputs[i] ∈ Alloc s := fun i => h_reads (Set.mem_iUnion.mpr ⟨i, rfl⟩)
  refine ⟨honestRow env₀ s g inputs k, fun c hc => ?_, ?_⟩
  · simp only [honestRow, mem_alloc] at hc ⊢
    rw [if_neg (Nat.ne_of_lt hc)]
  · have h_in : (inCells g s).map (honestRow env₀ s g inputs k) = inputs.map (honestRow env₀ s g inputs k) := by
      ext i hi
      have h_lt : inputs[i].1 < s := h_inputs ⟨i, hi⟩
      simp only [Vector.getElem_map, inCells, Vector.getElem_ofFn, honestRow, if_true, dif_pos hi,
        if_neg (Nat.ne_of_lt h_lt)]
    have h_in₀ : inputs.map (honestRow env₀ s g inputs k) = inputs.map env₀ :=
      map_congr_of_agree _ h_inputs fun c hc => by
        simp only [honestRow, mem_alloc] at hc ⊢; rw [if_neg (Nat.ne_of_lt hc)]
    refine ⟨h_in, ?_⟩
    rw [h_in, h_in₀]
    ext o ho
    simp only [Vector.getElem_map, outCells, Vector.getElem_ofFn, honestRow, if_true,
      dif_neg (Nat.not_lt.mpr (Nat.le_add_right _ _)), Nat.add_sub_cancel_left, dif_pos ho]

end Plonkish

-- `implicit_reducible`: see `ExprBackend`
@[implicit_reducible]
def Plonkish (F : Type) [Field F] : Backend where
  Native := F
  Cell := ℕ × ℕ
  Var := ℕ × ℕ
  eval env c := env c
  footprint c := {c}
  eval_frame _ _ c h := h c rfl
  State := ℕ
  Alloc := Plonkish.Alloc
  Op := PlonkishOp F
  advance _ s := s + 1
  alloc_mono _ s := Plonkish.alloc_mono_succ s
  reads := Plonkish.reads
  writes := Plonkish.writes
  writes_fresh op s := by
    obtain ⟨g, inputs, k⟩ := op
    constructor
    · rw [Set.disjoint_left]
      rintro c ⟨hc, _⟩ hc'
      simp only [Plonkish.mem_alloc] at hc'
      omega
    · rintro c ⟨hc, _⟩
      simp only [Plonkish.mem_alloc]
      omega
  Holds := Plonkish.Holds
  Honest := Plonkish.Honest
  honest_frame := Plonkish.honest_frame
  honest_extend := Plonkish.honest_extend

/-- The native values of the plonkish backend are the field it is built over. -/
instance : Field (Plonkish F).Native := ‹Field F›

namespace Plonkish

/-! The backend's definition, as simp lemmas. -/
@[circuit_norm] theorem eval_def (env : ℕ × ℕ → F) (c : ℕ × ℕ) : (Plonkish F).eval env c = env c := rfl
@[circuit_norm] theorem map_eval {m : ℕ} (env : ℕ × ℕ → F) (v : Vector (ℕ × ℕ) m) :
    v.map ((Plonkish F).eval env) = v.map env := rfl
@[circuit_norm] theorem footprint_def (c : ℕ × ℕ) : (Plonkish F).footprint c = {c} := rfl
@[circuit_norm] theorem alloc_def (s : ℕ) : (Plonkish F).Alloc s = Alloc s := rfl
@[circuit_norm] theorem advance_gate (g : Gate F) (inputs : Vector (ℕ × ℕ) g.nIn) (k : Vector F g.nFixed) (s : ℕ) :
    (Plonkish F).advance (.gate g inputs k) s = s + 1 := rfl
@[circuit_norm] theorem reads_gate (g : Gate F) (inputs : Vector (ℕ × ℕ) g.nIn) (k : Vector F g.nFixed) :
    (Plonkish F).reads (.gate g inputs k) = (Plonkish F).footprintT (M := natives g.nIn) inputs := by
  ext c
  simp only [Backend.footprintT_natives, footprint_def]
  rfl
@[circuit_norm] theorem holds_gate (env : ℕ × ℕ → F) (s : ℕ) (g : Gate F) (inputs : Vector (ℕ × ℕ) g.nIn)
    (k : Vector F g.nFixed) :
    (Plonkish F).Holds env s (.gate g inputs k) =
      ((inCells g s).map env = inputs.map env ∧
        g.Constraint ((inCells g s).map env) k ((outCells g s).map env)) := rfl
@[circuit_norm] theorem honest_gate (env : ℕ × ℕ → F) (s : ℕ) (g : Gate F) (inputs : Vector (ℕ × ℕ) g.nIn)
    (k : Vector F g.nFixed) :
    (Plonkish F).Honest env s (.gate g inputs k) =
      ((inCells g s).map env = inputs.map env ∧
        (outCells g s).map env = g.witness ((inCells g s).map env) k) := rfl

theorem footprintT_outCells (g : Gate F) (s : ℕ) :
    (Plonkish F).footprintT (M := natives g.nOut) (outCells g s) ⊆ Alloc (s + 1) := by
  rw [Backend.footprintT_natives]
  refine Set.iUnion_subset fun o => ?_
  rw [footprint_def, Set.singleton_subset_iff]
  exact outCells_mem g s o

/-- Place a gate. Its outputs are the output cells of the new row. -/
@[circuit_norm]
def place (g : Gate F) (inputs : Vector (ℕ × ℕ) g.nIn) (k : Vector F g.nFixed) :
    Circuit (Plonkish F) (Vector (ℕ × ℕ) g.nOut) :=
  fun s => (outCells g s, [.native (.gate g inputs k)])

/-- Every gate, at every assignment of its fixed cells: what the backend has natively. The
contract is the gate's own polynomial identities. -/
def gate (g : Gate F) (k : Vector F g.nFixed) : Impl (Plonkish F) (g.member k) where
  main inputs := place g inputs k
  spatial := by
    intro inputs s h
    simp only [circuit_norm]
    exact ⟨h, footprintT_outCells g s⟩
  soundness := by
    intro s env inputs _ h
    simp only [circuit_norm] at h ⊢
    rw [← h.1]
    exact h.2
  completeness := by
    intro s env inputs h h_prover
    simp only [circuit_norm] at h h_prover ⊢
    obtain ⟨h_in, h_out⟩ := h
    refine ⟨⟨h_in, ?_⟩, ?_⟩
    · rw [h_out, h_in]
      exact h_prover
    · rw [h_out, h_in]

omit [Field F] in
/-- What the permutation argument gives, cell by cell. -/
theorem copy_getElem {g : Gate F} {s : ℕ} {inputs : Vector (ℕ × ℕ) g.nIn} {env : ℕ × ℕ → F}
    (h : (inCells g s).map env = inputs.map env) (i : ℕ) (hi : i < g.nIn) :
    env (inCells g s)[i] = env inputs[i] := by
  have := congrArg (fun v => v[i]) h
  simpa using this

/-! ## The arithmetic vocabulary, from gates

One gate per functionality, and a row per operation: nothing is free. Every gate here has one
identity; the proofs unfold it and use the copy constraints. -/

@[reducible]
def addGate : Gate F := ⟨⟨2, 0, 1, [.output 0 - (.input 0 + .input 1)]⟩, fun x _ => #v[x[0] + x[1]]⟩
@[reducible]
def subGate : Gate F := ⟨⟨2, 0, 1, [.output 0 - (.input 0 - .input 1)]⟩, fun x _ => #v[x[0] - x[1]]⟩
@[reducible]
def mulGate : Gate F := ⟨⟨2, 0, 1, [.output 0 - .input 0 * .input 1]⟩, fun x _ => #v[x[0] * x[1]]⟩
/-- The scalar is a fixed cell: one gate for every scalar. -/
@[reducible]
def scaleGate : Gate F := ⟨⟨1, 1, 1, [.output 0 - .fixed 0 * .input 0]⟩, fun x k => #v[k[0] * x[0]]⟩
/-- The constant is a fixed cell: one gate for every constant. -/
@[reducible]
def constGate : Gate F := ⟨⟨0, 1, 1, [.output 0 - .fixed 0]⟩, fun _ k => #v[k[0]]⟩
/-- An assertion: no outputs. -/
@[reducible]
def mulEqGate : Gate F := ⟨⟨3, 0, 0, [.input 0 * .input 1 - .input 2]⟩, fun _ _ => #v[]⟩
@[reducible]
def assertZeroGate : Gate F := ⟨⟨1, 0, 0, [.input 0]⟩, fun _ _ => #v[]⟩
/-- A witness: no identities. -/
@[reducible]
def witnessGate (n : ℕ) (f : Vector F n → F) : Gate F := ⟨⟨n, 0, 1, []⟩, fun x _ => #v[f x]⟩

/-- The proof pattern of every gate below: expose the copy constraints and the identity. -/
syntax "gate_norm" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| gate_norm $[$loc]?) => `(tactic| simp only [circuit_norm, Gate.Constraint, List.forall_mem_singleton,
      List.not_mem_nil, false_implies, implies_true, GateExpr.eval_hsub, GateExpr.eval_hadd, GateExpr.eval_hmul,
      GateExpr.eval, Vector.getElem_map, Fin.getElem_fin, sub_eq_zero] $[$loc]?)

def add : Impl (Plonkish F) Add.interface where
  main | (a, b) => do
    let y ← gate (addGate (F := F)) #v[] #v[a, b]
    return y[0]
  spatial := by
    intro (a, b) s h
    simp only [circuit_norm, Set.union_subset_iff] at h ⊢
    exact ⟨h, fun h_post _ => Backend.footprint_getElem_subset h_post 0 Nat.one_pos⟩
  soundness := by
    intro s env (a, b) _ h
    gate_norm at h ⊢
    simpa using h
  completeness := by
    intro s env (a, b) _ _
    gate_norm
    simp

def sub : Impl (Plonkish F) Sub.interface where
  main | (a, b) => do
    let y ← gate (subGate (F := F)) #v[] #v[a, b]
    return y[0]
  spatial := by
    intro (a, b) s h
    simp only [circuit_norm, Set.union_subset_iff] at h ⊢
    exact ⟨h, fun h_post _ => Backend.footprint_getElem_subset h_post 0 Nat.one_pos⟩
  soundness := by
    intro s env (a, b) _ h
    gate_norm at h ⊢
    simpa using h
  completeness := by
    intro s env (a, b) _ _
    gate_norm
    simp

def mul : Impl (Plonkish F) Mul.interface where
  main | (a, b) => do
    let y ← gate (mulGate (F := F)) #v[] #v[a, b]
    return y[0]
  spatial := by
    intro (a, b) s h
    simp only [circuit_norm, Set.union_subset_iff] at h ⊢
    exact ⟨h, fun h_post _ => Backend.footprint_getElem_subset h_post 0 Nat.one_pos⟩
  soundness := by
    intro s env (a, b) _ h
    gate_norm at h ⊢
    simpa using h
  completeness := by
    intro s env (a, b) _ _
    gate_norm
    simp

/-- One implementation for every scalar. -/
def scale (c : F) : Impl (Plonkish F) (Scale.interface c) where
  main x := do
    let y ← gate (scaleGate (F := F)) #v[c] #v[x]
    return y[0]
  spatial := by
    intro x s h
    simp only [circuit_norm] at h ⊢
    exact ⟨h, fun h_post _ => Backend.footprint_getElem_subset h_post 0 Nat.one_pos⟩
  soundness := by
    intro s env x _ h
    gate_norm at h ⊢
    simpa using h
  completeness := by
    intro s env x _ _
    gate_norm
    simp

/-- One implementation for every constant. -/
def const (c : F) : Impl (Plonkish F) (Const.interface c) where
  main _ := do
    let y ← gate (constGate (F := F)) #v[c] #v[]
    return y[0]
  spatial := by
    intro _ s _
    simp only [circuit_norm]
    exact ⟨Set.empty_subset _, fun h_post _ => Backend.footprint_getElem_subset h_post 0 Nat.one_pos⟩
  soundness := by
    intro s env _ _ h
    gate_norm at h ⊢
    simpa using h
  completeness := by
    intro s env _ _ _
    gate_norm
    simp

def mulEq : Impl (Plonkish F) MulEq.interface where
  main | (a, b, c) => do
    let _ ← gate (mulEqGate (F := F)) #v[] #v[a, b, c]
    return ()
  spatial := by
    intro (a, b, c) s h
    simp only [circuit_norm, Set.union_subset_iff] at h ⊢
    exact ⟨h, fun _ _ => Set.empty_subset _⟩
  soundness := by
    intro s env (a, b, c) _ h
    gate_norm at h ⊢
    simpa using h
  completeness := by
    intro s env (a, b, c) _ h_prover
    gate_norm at h_prover ⊢
    simpa using h_prover

def assertZeroImpl : Impl (Plonkish F) AssertZero.interface where
  main x := do
    let _ ← gate (assertZeroGate (F := F)) #v[] #v[x]
    return ()
  spatial := by
    intro x s h
    simp only [circuit_norm] at h ⊢
    exact ⟨h, fun _ _ => Set.empty_subset _⟩
  soundness := by
    intro s env x _ h
    gate_norm at h ⊢
    simpa using h
  completeness := by
    intro s env x _ h_prover
    gate_norm at h_prover ⊢
    simpa using h_prover

/-- One implementation for every witness computation, over any input shape. -/
def witnessImpl (p : Witness.Params F) : Impl (Plonkish F) (Witness.interface p) where
  main input := do
    let y ← gate (witnessGate (F := F) (size p.Input) fun v => p.f (fromElements v)) #v[] (toElements input)
    return y[0]
  spatial := by
    intro input s h
    simp only [circuit_norm] at h ⊢
    exact ⟨h, fun h_post _ => Backend.footprint_getElem_subset h_post 0 Nat.one_pos⟩
  soundness := by
    intro s env input _ _
    simp only [circuit_norm]
  completeness := by
    intro s env input h _
    gate_norm at h ⊢
    have h := congrArg (fun v => v[0]) h
    simp only [Vector.getElem_map] at h
    rw [h, ProvableType.map_eq_fromElements]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
    rfl

/-- The plonkish backend implements all of `Arith.interface` natively, a gate each. -/
def arith : ∀ n, Impl (Plonkish F) (Arith.interface n)
  | .add => add
  | .sub => sub
  | .mul => mul
  | .scale c => scale c
  | .const c => const c
  | .mulEq => mulEq
  | .assertZero => assertZeroImpl
  | @Arith.Name.witness _ Input inst f => letI := inst; witnessImpl ⟨Input, f⟩

/-! ## Cost: rows -/

/-- The cost of a plonkish circuit: its number of rows. Every operation is one row. -/
def rows : (Plonkish F).Measure ℕ where
  op _ := 1

@[circuit_norm] theorem rows_gate (g : Gate F) (inputs : Vector (ℕ × ℕ) g.nIn) (k : Vector F g.nFixed) :
    rows.op (.gate g inputs k) = 1 := rfl

instance (g : Gate F) (k : Vector F g.nFixed) : Impl.Measured rows (gate g k) where value := 1
instance : Impl.Measured rows (add (F := F)) where value := 1
instance : Impl.Measured rows (sub (F := F)) where value := 1
instance : Impl.Measured rows (mul (F := F)) where value := 1
instance (c : F) : Impl.Measured rows (scale c) where value := 1
instance (c : F) : Impl.Measured rows (const c) where value := 1
instance : Impl.Measured rows (mulEq (F := F)) where value := 1
instance : Impl.Measured rows (assertZeroImpl (F := F)) where value := 1
instance (p : Witness.Params F) : Impl.Measured rows (witnessImpl p) where value := 1

instance : ∀ n, Impl.Measured rows (arith (F := F) n)
  | .add => inferInstanceAs (Impl.Measured rows add)
  | .sub => inferInstanceAs (Impl.Measured rows sub)
  | .mul => inferInstanceAs (Impl.Measured rows mul)
  | .scale c => inferInstanceAs (Impl.Measured rows (scale c))
  | .const c => inferInstanceAs (Impl.Measured rows (const c))
  | .mulEq => inferInstanceAs (Impl.Measured rows mulEq)
  | .assertZero => inferInstanceAs (Impl.Measured rows assertZeroImpl)
  | @Arith.Name.witness _ Input inst f => letI := inst; inferInstanceAs (Impl.Measured rows (witnessImpl ⟨Input, f⟩))

@[simp] theorem rows_of_gate (g : Gate F) (k : Vector F g.nFixed) : rows.of (gate g k) = 1 := rfl
/-- Every arithmetic functionality is one row. -/
@[simp] theorem rows_of_arith (n : Arith.Name F) : rows.of (arith n) = 1 := by
  cases n <;> rfl

/-! ## The configuration, read off the operations -/

/-- The gate an operation places. -/
def _root_.Clean2.PlonkishOp.shape : PlonkishOp F → GateShape F
  | .gate g .. => g.toGateShape

/-- The configuration of a list of native operations: the distinct gates it places, in order of
first use. This is what Halo2's `configure` declares, and what the verifying key is built from. -/
def config [DecidableEq F] (ops : List (PlonkishOp F)) : List (GateShape F) :=
  (ops.map PlonkishOp.shape).dedup

end Plonkish
end Clean2
