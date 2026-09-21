/-
Interfaces and implementations.

- An `Interface Native Params` is a family of members indexed by compile-time parameters: a
  vector length, a constant, a witness computation, a name in a vocabulary. An interface with
  no parameters is one with `Params := Unit`.
- An `Interface.Member` is one semantic contract on values: input and output shapes, assumptions
  and specs, for both the verifier side (soundness) and the prover side (completeness). It does
  not mention any backend, circuit, or heap.
- An `Impl B I` implements every member of the family on backend `B`: for each parameter, a
  circuit together with proofs that it meets that member, and a proof of the (uniform) spatial
  contract: given its inputs exist, it is well-formed and its outputs exist afterwards.
- `Impl.call` uses an implementation as a subcircuit, at one parameter: the parent only sees
  the member. The same implementation can be called at several parameters in one circuit.
-/
module

public import Clean2.Core.Circuit
public import Clean2.Core.Spatial

@[expose] public section

namespace Clean2
universe u v

/-- One member of an interface: the shapes of the input and output, and the semantic contract on
them. -/
structure Interface.Member (Native : Type) where
  Input : TypeMap
  Output : TypeMap
  [instInput : ProvableType Input]
  [instOutput : ProvableType Output]
  /-- assumed for soundness -/
  Assumptions : Input Native → Prop := fun _ => True
  /-- proved by soundness -/
  Spec : Input Native → Output Native → Prop := fun _ _ => True
  /-- assumed for completeness ("what the honest prover guarantees about the inputs") -/
  ProverAssumptions : Input Native → Prop := fun _ => True
  /-- proved by completeness ("what the honest prover knows about the output") -/
  ProverSpec : Input Native → Output Native → Prop := fun _ _ => True

attribute [instance] Interface.Member.instInput Interface.Member.instOutput

/-- A formal interface: a family of members indexed by compile-time parameters. -/
abbrev Interface (Native : Type) (Params : Type u) := Params → Interface.Member Native

namespace Interface
variable {Native : Type}

/-- A sub-interface: the members reachable through a renaming of the parameters. -/
abbrev restrict {Params : Type u} {Params' : Type v} (I : Interface Native Params) (f : Params' → Params) :
    Interface Native Params' :=
  fun p => I (f p)

/-- Both families. -/
abbrev union {Params : Type u} {Params' : Type v} (I : Interface Native Params) (J : Interface Native Params') :
    Interface Native (Params ⊕ Params') :=
  Sum.elim I J

end Interface

section
variable {B : Backend}

/-- Soundness of `main` against `c`: under the assumptions, if the (proof-level) constraints
hold then the spec holds on the input and output. -/
@[circuit_norm]
def Soundness (B : Backend) (c : Interface.Member B.Native) (main : c.Input B.Var → Circuit B (c.Output B.Var))
    (output : c.Input B.Var → B.State → c.Output B.Var) : Prop :=
  ∀ (s : B.State) (env : B.Cell → B.Native) (input : c.Input B.Var),
    c.Assumptions (B.evalT env input) →
    ((main input).operations s).SoundnessHold env s →
    c.Spec (B.evalT env input) (B.evalT env (output input s))

/-- Completeness of `main` against `c`: if the prover is honest and the prover assumptions
hold, then the (proof-level) constraints hold and the prover spec holds. -/
@[circuit_norm]
def Completeness (B : Backend) (c : Interface.Member B.Native) (main : c.Input B.Var → Circuit B (c.Output B.Var))
    (output : c.Input B.Var → B.State → c.Output B.Var) : Prop :=
  ∀ (s : B.State) (env : B.Cell → B.Native) (input : c.Input B.Var),
    ((main input).operations s).HonestCompleteness env s →
    c.ProverAssumptions (B.evalT env input) →
    ((main input).operations s).CompletenessHold env s ∧
    c.ProverSpec (B.evalT env input) (B.evalT env (output input s))

/-- The spatial contract, the same for every implementation:
`{inputs exist} main {well-formed ∗ outputs exist}`. -/
@[circuit_norm]
def Spatial (B : Backend) (c : Interface.Member B.Native) (main : c.Input B.Var → Circuit B (c.Output B.Var))
    (output : c.Input B.Var → B.State → c.Output B.Var) : Prop :=
  ∀ (input : c.Input B.Var) (s : B.State), B.footprintT input ⊆ B.Alloc s →
    ((main input).operations s).LocalHold s fun s' => B.footprintT (output input s) ⊆ B.Alloc s'

variable {Params : Type u}

/-- An implementation of the interface `I` on backend `B`: a circuit for every parameter, with
its proofs. -/
structure Impl (B : Backend) (I : Interface B.Native Params) where
  main (p : Params) : (I p).Input B.Var → Circuit B ((I p).Output B.Var)
  /-- the allocation state after a call. Opaque to callers: no layout is visible here.
  Defaults to running the circuit; override to give it a closed form. -/
  advance (p : Params) : (I p).Input B.Var → B.State → B.State :=
    fun input s => ((main p input).operations s).advance s
  /-- the output, ideally in a form that does not require running `main` -/
  output (p : Params) : (I p).Input B.Var → B.State → (I p).Output B.Var :=
    fun input s => (main p input).output s
  advance_eq : ∀ p input s, ((main p input).operations s).advance s = advance p input s := by
    intros; rfl
  output_eq : ∀ p input s, (main p input).output s = output p input s := by
    intros; rfl
  consistent : ∀ p input s, ((main p input).operations s).Consistent s := by
    intros; simp only [circuit_norm]; try trivial
  spatial : ∀ p, Spatial B (I p) (main p) (output p) := by
    intro _; spatial
  soundness : ∀ p, Soundness B (I p) (main p) (output p)
  completeness : ∀ p, Completeness B (I p) (main p) (output p)

namespace Impl
variable {I : Interface B.Native Params}

/-- The member implemented by `impl` at a call site. This is the theorem that lets a caller forget
the implementation. -/
def toSubcircuit (impl : Impl B I) (p : Params) (s : B.State) (input : (I p).Input B.Var) : Subcircuit B s where
  ops := ((impl.main p input).operations s).toFlat
  next := impl.advance p input s
  next_eq := by rw [Ops.flatAdvance_toFlat (impl.consistent p input s), impl.advance_eq]
  Assumptions env := (I p).Assumptions (B.evalT env input)
  Spec env := (I p).Spec (B.evalT env input) (B.evalT env (impl.output p input s))
  ProverAssumptions env := (I p).ProverAssumptions (B.evalT env input)
  ProverSpec env :=
    (I p).ProverAssumptions (B.evalT env input) →
      ((I p).Assumptions (B.evalT env input) →
        (I p).Spec (B.evalT env input) (B.evalT env (impl.output p input s))) ∧
      (I p).ProverSpec (B.evalT env input) (B.evalT env (impl.output p input s))
  pre := B.footprintT input ⊆ B.Alloc s
  post := B.footprintT (impl.output p input s) ⊆ B.Alloc (impl.advance p input s)
  soundness env h_assumptions h_holds :=
    impl.soundness p s env input h_assumptions
      (Ops.soundnessHold_of_constraintsHold (impl.consistent p input s) h_holds)
  completeness env h_honest := by
    have h_consistent := impl.consistent p input s
    have h_honest' := Ops.honestCompleteness_of_honest h_consistent h_honest
    refine ⟨fun h_prover => ?_, fun h_prover => ⟨fun h_assumptions => ?_, ?_⟩⟩
    · exact Ops.constraintsHold_of_completenessHold h_consistent h_honest
        (impl.completeness p s env input h_honest' h_prover).1
    · exact impl.soundness p s env input h_assumptions
        (Ops.soundnessHold_of_constraintsHold h_consistent
          (Ops.constraintsHold_of_completenessHold h_consistent h_honest
            (impl.completeness p s env input h_honest' h_prover).1))
    · exact (impl.completeness p s env input h_honest' h_prover).2
  local_of_pre h := (Ops.local_of_localHold (impl.consistent p input s) (impl.spatial p input s h)).1
  post_of_pre h := by
    have := (Ops.local_of_localHold (impl.consistent p input s) (impl.spatial p input s h)).2
    rwa [impl.advance_eq] at this

/-- Use an implementation as a subcircuit, at parameter `p`. -/
@[circuit_norm]
def call (impl : Impl B I) (p : Params) (input : (I p).Input B.Var) : Circuit B ((I p).Output B.Var) :=
  fun s => (impl.output p input s, [.call (impl.toSubcircuit p s input)])

/-- `impl p input` calls `impl` at parameter `p`. -/
instance (priority := low) :
    CoeFun (Impl B I) (fun _ => (p : Params) → (I p).Input B.Var → Circuit B ((I p).Output B.Var)) :=
  ⟨call⟩

/-- An implementation of an interface without parameters is called as `impl input`. -/
instance (priority := high) {I : Interface B.Native Unit} :
    CoeFun (Impl B I) (fun _ => (I ()).Input B.Var → Circuit B ((I ()).Output B.Var)) :=
  ⟨fun impl => impl.call ()⟩

/-- An implementation of an interface all of whose members have no input is called as `impl p`.
The shape is matched through the (reducible) interface, so this applies to `const 1` but not to
`arith (.const 1)`, whose input shape depends on the name. -/
instance (priority := high + 1) {Output : Params → TypeMap} [inst : ∀ p, ProvableType (Output p)]
    {A PA : Params → Unit → Prop} {S PS : (p : Params) → Unit → Output p B.Native → Prop} :
    CoeFun (Impl B fun p => @Interface.Member.mk B.Native unit (Output p) inferInstance (inst p) (A p) (S p) (PA p) (PS p))
      (fun _ => (p : Params) → Circuit B (Output p B.Var)) :=
  ⟨fun impl p => impl.call p ()⟩

/-! What a caller sees of a call, in each of the proof-level semantics.

Interfaces are reducible definitions and are not in `circuit_norm`: `simp only [circuit_norm]`
turns each call into its member's `Assumptions`/`Spec` (etc.) through the lemmas below, and
reduces the projections `(X.interface p).Spec`, `(X.interface p).Input` of a reducible interface
on the spot. Interfaces must not be unfolded explicitly *before* the calls are taken apart: `simp`
would then unfold `X.interface` in the (dependent) `I` argument of `Impl.toSubcircuit` as well, after
which `impl : Impl B X.interface` no longer matches the lemmas below at reducible transparency. -/

@[circuit_norm]
theorem toSubcircuit_next (impl : Impl B I) (p : Params) (s : B.State) (input : (I p).Input B.Var) :
    (impl.toSubcircuit p s input).next = impl.advance p input s := rfl

@[circuit_norm]
theorem toSubcircuit_Assumptions (impl : Impl B I) (p : Params) (s : B.State) (input : (I p).Input B.Var)
    (env : B.Cell → B.Native) :
    (impl.toSubcircuit p s input).Assumptions env = (I p).Assumptions (B.evalT env input) := rfl

@[circuit_norm]
theorem toSubcircuit_Spec (impl : Impl B I) (p : Params) (s : B.State) (input : (I p).Input B.Var)
    (env : B.Cell → B.Native) :
    (impl.toSubcircuit p s input).Spec env =
      (I p).Spec (B.evalT env input) (B.evalT env (impl.output p input s)) := rfl

@[circuit_norm]
theorem toSubcircuit_ProverAssumptions (impl : Impl B I) (p : Params) (s : B.State) (input : (I p).Input B.Var)
    (env : B.Cell → B.Native) :
    (impl.toSubcircuit p s input).ProverAssumptions env = (I p).ProverAssumptions (B.evalT env input) := rfl

@[circuit_norm]
theorem toSubcircuit_ProverSpec (impl : Impl B I) (p : Params) (s : B.State) (input : (I p).Input B.Var)
    (env : B.Cell → B.Native) :
    (impl.toSubcircuit p s input).ProverSpec env =
      ((I p).ProverAssumptions (B.evalT env input) →
        ((I p).Assumptions (B.evalT env input) →
          (I p).Spec (B.evalT env input) (B.evalT env (impl.output p input s))) ∧
        (I p).ProverSpec (B.evalT env input) (B.evalT env (impl.output p input s))) := rfl

@[circuit_norm]
theorem toSubcircuit_pre (impl : Impl B I) (p : Params) (s : B.State) (input : (I p).Input B.Var) :
    (impl.toSubcircuit p s input).pre = (B.footprintT input ⊆ B.Alloc s) := rfl

@[circuit_norm]
theorem toSubcircuit_post (impl : Impl B I) (p : Params) (s : B.State) (input : (I p).Input B.Var) :
    (impl.toSubcircuit p s input).post =
      (B.footprintT (impl.output p input s) ⊆ B.Alloc (impl.advance p input s)) := rfl

/-! ### Witness generation, and the completeness statement it makes non-vacuous -/

/-- An honest environment exists on top of any assignment of the existing heap. -/
theorem honest_env_exists (impl : Impl B I) (p : Params) (input : (I p).Input B.Var) (s : B.State)
    (env₀ : B.Cell → B.Native) (h_in : B.footprintT input ⊆ B.Alloc s) :
    ∃ env, (∀ c ∈ B.Alloc s, env c = env₀ c) ∧ ((impl.main p input).operations s).Honest env s :=
  Backend.flatHonest_exists _ s env₀
    (Ops.local_of_localHold (impl.consistent p input s) (impl.spatial p input s h_in)).1

/-- Completeness, as a statement about the real constraints: for inputs that exist in the heap
and satisfy the prover assumptions, some honest environment (agreeing with the given one on the
existing heap) satisfies all constraints, and the prover spec holds there. -/
theorem exists_honest_env (impl : Impl B I) (p : Params) (input : (I p).Input B.Var) (s : B.State)
    (env₀ : B.Cell → B.Native) (h_in : B.footprintT input ⊆ B.Alloc s)
    (h_prover : (I p).ProverAssumptions (B.evalT env₀ input)) :
    ∃ env, (∀ c ∈ B.Alloc s, env c = env₀ c) ∧
      ((impl.main p input).operations s).ConstraintsHold env s ∧
      (I p).ProverSpec (B.evalT env input) (B.evalT env (impl.output p input s)) := by
  obtain ⟨env, h_agree, h_honest⟩ := impl.honest_env_exists p input s env₀ h_in
  have h_consistent := impl.consistent p input s
  have h_prover' : (I p).ProverAssumptions (B.evalT env input) := by
    rwa [Backend.evalT_frame env env₀ input fun c hc => h_agree c (h_in hc)]
  have h := impl.completeness p s env input (Ops.honestCompleteness_of_honest h_consistent h_honest) h_prover'
  exact ⟨env, h_agree, Ops.constraintsHold_of_completenessHold h_consistent h_honest h.1, h.2⟩

/-! ### Combinators on implementations: instantiation is function application -/

/-- The implementation of a sub-interface. -/
def restrict {Params' : Type v} (impl : Impl B I) (f : Params' → Params) : Impl B (I.restrict f) where
  main p := impl.main (f p)
  advance p := impl.advance (f p)
  output p := impl.output (f p)
  advance_eq p := impl.advance_eq (f p)
  output_eq p := impl.output_eq (f p)
  consistent p := impl.consistent (f p)
  spatial p := impl.spatial (f p)
  soundness p := impl.soundness (f p)
  completeness p := impl.completeness (f p)

/-- `impl.fix p`: the implementation of the single member `I p`, an interface without parameters. -/
abbrev fix (impl : Impl B I) (p : Params) : Impl B (fun _ : Unit => I p) :=
  impl.restrict fun _ => p

/-- Assemble an implementation of a family from an implementation of each member. -/
def ofFun (impls : (p : Params) → Impl B (fun _ : Unit => I p)) : Impl B I where
  main p := (impls p).main ()
  advance p := (impls p).advance ()
  output p := (impls p).output ()
  advance_eq p := (impls p).advance_eq ()
  output_eq p := (impls p).output_eq ()
  consistent p := (impls p).consistent ()
  spatial p := (impls p).spatial ()
  soundness p := (impls p).soundness ()
  completeness p := (impls p).completeness ()

/-- Implementations of two families. -/
def union {Params' : Type v} {J : Interface B.Native Params'} (x : Impl B I) (y : Impl B J) :
    Impl B (I.union J) where
  main | .inl p => x.main p | .inr p => y.main p
  advance | .inl p => x.advance p | .inr p => y.advance p
  output | .inl p => x.output p | .inr p => y.output p
  advance_eq | .inl p => x.advance_eq p | .inr p => y.advance_eq p
  output_eq | .inl p => x.output_eq p | .inr p => y.output_eq p
  consistent | .inl p => x.consistent p | .inr p => y.consistent p
  spatial | .inl p => x.spatial p | .inr p => y.spatial p
  soundness | .inl p => x.soundness p | .inr p => y.soundness p
  completeness | .inl p => x.completeness p | .inr p => y.completeness p

end Impl
end

/-! ### Refinement: an implementation of a stronger member implements a weaker one -/

/-- `c.refine`: the same shapes, another contract. -/
abbrev Interface.Member.refine {Native : Type} (c : Interface.Member Native)
    (Assumptions : c.Input Native → Prop) (Spec : c.Input Native → c.Output Native → Prop)
    (ProverAssumptions : c.Input Native → Prop) (ProverSpec : c.Input Native → c.Output Native → Prop) :
    Interface.Member Native :=
  { c with Assumptions, Spec, ProverAssumptions, ProverSpec }

/-- `c.Refines A S PA PS`: `c` assumes less and promises more than the contract `A S PA PS`. -/
structure Interface.Member.Refines {Native : Type} (c : Interface.Member Native)
    (Assumptions : c.Input Native → Prop) (Spec : c.Input Native → c.Output Native → Prop)
    (ProverAssumptions : c.Input Native → Prop) (ProverSpec : c.Input Native → c.Output Native → Prop) :
    Prop where
  assumptions : ∀ x, Assumptions x → c.Assumptions x
  spec : ∀ x y, Assumptions x → c.Spec x y → Spec x y
  proverAssumptions : ∀ x, ProverAssumptions x → c.ProverAssumptions x
  proverSpec : ∀ x y, ProverAssumptions x → c.ProverSpec x y → ProverSpec x y

def Impl.refine {B : Backend} {Params : Type u} {I : Interface B.Native Params} (impl : Impl B I)
    {Assumptions : ∀ p, (I p).Input B.Native → Prop} {Spec : ∀ p, (I p).Input B.Native → (I p).Output B.Native → Prop}
    {ProverAssumptions : ∀ p, (I p).Input B.Native → Prop}
    {ProverSpec : ∀ p, (I p).Input B.Native → (I p).Output B.Native → Prop}
    (h : ∀ p, (I p).Refines (Assumptions p) (Spec p) (ProverAssumptions p) (ProverSpec p)) :
    Impl B (fun p => (I p).refine (Assumptions p) (Spec p) (ProverAssumptions p) (ProverSpec p)) where
  main := impl.main
  advance := impl.advance
  output := impl.output
  advance_eq := impl.advance_eq
  output_eq := impl.output_eq
  consistent := impl.consistent
  spatial := impl.spatial
  soundness p s env input h_assumptions h_holds :=
    (h p).spec _ _ h_assumptions (impl.soundness p s env input ((h p).assumptions _ h_assumptions) h_holds)
  completeness p s env input h_honest h_prover :=
    let r := impl.completeness p s env input h_honest ((h p).proverAssumptions _ h_prover)
    ⟨r.1, (h p).proverSpec _ _ h_prover r.2⟩

end Clean2
