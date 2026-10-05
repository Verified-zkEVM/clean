/-
Interfaces and implementations.

- An `Interface` is one semantic contract on values: a synthetic input type and a synthetic
  output type (`CType.lean`), and assumptions and specs on their meanings, for both the verifier
  side (soundness) and the prover side (completeness). It does not mention any backend, circuit,
  or heap. A family of interfaces, indexed by compile-time parameters (a vector length, a
  constant, a witness computation, a name in a vocabulary), is a function into interfaces; a
  generic type (a byte, a digest) is an argument of the interface's definition, so that an
  implementation exists at one layout and the layers above are generic in it.
- An `Impl B c` implements the interface `c` on backend `B`: a circuit together with proofs that
  it meets `c`, and a proof of the (uniform) spatial contract: given its inputs exist, it is
  well-formed and its outputs exist afterwards. An implementation of a family is a function into
  implementations.
- `Impl.call` uses an implementation as a subcircuit: the parent only sees the interface.
-/
module

public import Clean2.Core.Circuit
public import Clean2.Core.Spatial
public import Clean2.Core.CType

@[expose] public section

namespace Clean2

/-- One contract: the synthetic types of the input and output, and the semantic contract on their
meanings. A contract on native values names `.native`, `.nativePair`, `.natives n`, ...; a
contract on bytes names a `byte : CType Native UInt8` it was given, and is the same contract
whatever a byte is made of. -/
structure Interface (Native : Type) where
  /-- the meaning of the input -/
  input : Type
  /-- how an `input` is laid out in native values -/
  inputCType : CType Native input
  /-- the meaning of the output -/
  output : Type
  /-- how an `output` is laid out in native values -/
  outputCType : CType Native output
  /-- assumed for soundness -/
  Assumptions : input → Prop := fun _ => True
  /-- proved by soundness -/
  Spec : input → output → Prop := fun _ _ => True
  /-- assumed for completeness ("what the honest prover guarantees about the inputs") -/
  ProverAssumptions : input → Prop := fun _ => True
  /-- proved by completeness ("what the honest prover knows about the output") -/
  ProverSpec : input → output → Prop := fun _ _ => True

namespace Interface
variable {Native : Type} (c : Interface Native)

/-- The layout of the input. `c.Input B.Var` is what an implementation takes, `c.Input Native`
what it denotes. -/
abbrev Input : TypeMap := c.inputCType.Shape
/-- The layout of the output. -/
abbrev Output : TypeMap := c.outputCType.Shape

end Interface

section
variable {B : Backend}

/-! The contracts are stated on meanings; soundness and completeness are stated on native values,
through the synthetic types: the representation invariant is assumed of the inputs and proved of
the outputs, on both sides, and the contract is applied to what the values decode to. -/

/-- Soundness of `main` against `c`: for a valid input satisfying the assumptions, if the
(proof-level) constraints hold then the output is valid and the spec holds on their meanings. -/
@[circuit_norm]
def Soundness (B : Backend) (c : Interface B.Native) (main : c.Input B.Var → Circuit B (c.Output B.Var))
    (output : c.Input B.Var → B.State → c.Output B.Var) : Prop :=
  ∀ (s : B.State) (env : B.Cell → B.Native) (input : c.Input B.Var),
    c.inputCType.Valid (B.evalT env input) ∧ c.Assumptions (c.inputCType.decode (B.evalT env input)) →
    ((main input).operations s).SoundnessHold env s →
    c.outputCType.Valid (B.evalT env (output input s)) ∧
      c.Spec (c.inputCType.decode (B.evalT env input)) (c.outputCType.decode (B.evalT env (output input s)))

/-- Completeness of `main` against `c`: if the prover is honest, and the input is valid and
satisfies the prover assumptions, then the (proof-level) constraints hold, the output is valid,
and the prover spec holds on their meanings. -/
@[circuit_norm]
def Completeness (B : Backend) (c : Interface B.Native) (main : c.Input B.Var → Circuit B (c.Output B.Var))
    (output : c.Input B.Var → B.State → c.Output B.Var) : Prop :=
  ∀ (s : B.State) (env : B.Cell → B.Native) (input : c.Input B.Var),
    ((main input).operations s).HonestCompleteness env s →
    c.inputCType.Valid (B.evalT env input) ∧ c.ProverAssumptions (c.inputCType.decode (B.evalT env input)) →
    ((main input).operations s).CompletenessHold env s ∧
    c.outputCType.Valid (B.evalT env (output input s)) ∧
      c.ProverSpec (c.inputCType.decode (B.evalT env input)) (c.outputCType.decode (B.evalT env (output input s)))

/-- The spatial contract, the same for every implementation:
`{inputs exist} main {well-formed ∗ outputs exist}`. -/
@[circuit_norm]
def Spatial (B : Backend) (c : Interface B.Native) (main : c.Input B.Var → Circuit B (c.Output B.Var))
    (output : c.Input B.Var → B.State → c.Output B.Var) : Prop :=
  ∀ (input : c.Input B.Var) (s : B.State), B.footprintT input ⊆ B.Alloc s →
    ((main input).operations s).LocalHold s fun s' => B.footprintT (output input s) ⊆ B.Alloc s'

/-- An implementation of the interface `c` on backend `B`: a circuit, with its proofs. -/
structure Impl (B : Backend) (c : Interface B.Native) where
  main : c.Input B.Var → Circuit B (c.Output B.Var)
  /-- the allocation state after a call. Opaque to callers: no layout is visible here.
  Defaults to running the circuit; override to give it a closed form. -/
  advance : c.Input B.Var → B.State → B.State :=
    fun input s => ((main input).operations s).advance s
  /-- the output, ideally in a form that does not require running `main` -/
  output : c.Input B.Var → B.State → c.Output B.Var :=
    fun input s => (main input).output s
  advance_eq : ∀ input s, ((main input).operations s).advance s = advance input s := by
    intros; rfl
  output_eq : ∀ input s, (main input).output s = output input s := by
    intros; rfl
  consistent : ∀ input s, ((main input).operations s).Consistent s := by
    intros; simp only [circuit_norm]; try trivial
  spatial : Spatial B c main output := by
    spatial
  soundness : Soundness B c main output
  completeness : Completeness B c main output

namespace Impl
variable {c : Interface B.Native}

/-- The contract implemented by `impl` at a call site. This is the theorem that lets a caller
forget the implementation. -/
def toSubcircuit (impl : Impl B c) (s : B.State) (input : c.Input B.Var) : Subcircuit B s where
  ops := ((impl.main input).operations s).toFlat
  next := impl.advance input s
  next_eq := by rw [Ops.flatAdvance_toFlat (impl.consistent input s), impl.advance_eq]
  Assumptions env := c.inputCType.Valid (B.evalT env input) ∧ c.Assumptions (c.inputCType.decode (B.evalT env input))
  Spec env := c.outputCType.Valid (B.evalT env (impl.output input s)) ∧
    c.Spec (c.inputCType.decode (B.evalT env input)) (c.outputCType.decode (B.evalT env (impl.output input s)))
  ProverAssumptions env :=
    c.inputCType.Valid (B.evalT env input) ∧ c.ProverAssumptions (c.inputCType.decode (B.evalT env input))
  ProverSpec env :=
    c.inputCType.Valid (B.evalT env input) ∧ c.ProverAssumptions (c.inputCType.decode (B.evalT env input)) →
      (c.inputCType.Valid (B.evalT env input) ∧ c.Assumptions (c.inputCType.decode (B.evalT env input)) →
        c.outputCType.Valid (B.evalT env (impl.output input s)) ∧
          c.Spec (c.inputCType.decode (B.evalT env input)) (c.outputCType.decode (B.evalT env (impl.output input s)))) ∧
      c.outputCType.Valid (B.evalT env (impl.output input s)) ∧
        c.ProverSpec (c.inputCType.decode (B.evalT env input)) (c.outputCType.decode (B.evalT env (impl.output input s)))
  pre := B.footprintT input ⊆ B.Alloc s
  post := B.footprintT (impl.output input s) ⊆ B.Alloc (impl.advance input s)
  soundness env h_assumptions h_holds :=
    impl.soundness s env input h_assumptions
      (Ops.soundnessHold_of_constraintsHold (impl.consistent input s) h_holds)
  completeness env h_honest := by
    have h_consistent := impl.consistent input s
    have h_honest' := Ops.honestCompleteness_of_honest h_consistent h_honest
    refine ⟨fun h_prover => ?_, fun h_prover => ⟨fun h_assumptions => ?_, ?_⟩⟩
    · exact Ops.constraintsHold_of_completenessHold h_consistent h_honest
        (impl.completeness s env input h_honest' h_prover).1
    · exact impl.soundness s env input h_assumptions
        (Ops.soundnessHold_of_constraintsHold h_consistent
          (Ops.constraintsHold_of_completenessHold h_consistent h_honest
            (impl.completeness s env input h_honest' h_prover).1))
    · exact (impl.completeness s env input h_honest' h_prover).2
  local_of_pre h := (Ops.local_of_localHold (impl.consistent input s) (impl.spatial input s h)).1
  post_of_pre h := by
    have := (Ops.local_of_localHold (impl.consistent input s) (impl.spatial input s h)).2
    rwa [impl.advance_eq] at this

/-- Use an implementation as a subcircuit. -/
@[circuit_norm]
def call (impl : Impl B c) (input : c.Input B.Var) : Circuit B (c.Output B.Var) :=
  fun s => (impl.output input s, [.call (impl.toSubcircuit s input)])

/-- `impl input` calls `impl`. An implementation of a family is a function, so `impl p input`
calls it at parameter `p`; an interface without input is called as `impl ()`. -/
instance : CoeFun (Impl B c) (fun _ => c.Input B.Var → Circuit B (c.Output B.Var)) :=
  ⟨call⟩

/-! What a caller sees of a call, in each of the proof-level semantics.

Interfaces are reducible definitions and are not in `circuit_norm`: `simp only [circuit_norm]`
turns each call into its interface's `Assumptions`/`Spec` (etc.) through the lemmas below, and
reduces the projections `(X.interface p).Spec`, `(X.interface p).input` of a reducible interface
on the spot. Interfaces must not be unfolded explicitly *before* the calls are taken apart: `simp`
would then unfold `X.interface` in the (dependent) `c` argument of `Impl.toSubcircuit` as well, after
which `impl : Impl B X.interface` no longer matches the lemmas below at reducible transparency. -/

@[circuit_norm]
theorem toSubcircuit_next (impl : Impl B c) (s : B.State) (input : c.Input B.Var) :
    (impl.toSubcircuit s input).next = impl.advance input s := rfl

@[circuit_norm]
theorem toSubcircuit_Assumptions (impl : Impl B c) (s : B.State) (input : c.Input B.Var)
    (env : B.Cell → B.Native) :
    (impl.toSubcircuit s input).Assumptions env =
      (c.inputCType.Valid (B.evalT env input) ∧ c.Assumptions (c.inputCType.decode (B.evalT env input))) := rfl

@[circuit_norm]
theorem toSubcircuit_Spec (impl : Impl B c) (s : B.State) (input : c.Input B.Var)
    (env : B.Cell → B.Native) :
    (impl.toSubcircuit s input).Spec env =
      (c.outputCType.Valid (B.evalT env (impl.output input s)) ∧
        c.Spec (c.inputCType.decode (B.evalT env input)) (c.outputCType.decode (B.evalT env (impl.output input s)))) := rfl

@[circuit_norm]
theorem toSubcircuit_ProverAssumptions (impl : Impl B c) (s : B.State) (input : c.Input B.Var)
    (env : B.Cell → B.Native) :
    (impl.toSubcircuit s input).ProverAssumptions env =
      (c.inputCType.Valid (B.evalT env input) ∧ c.ProverAssumptions (c.inputCType.decode (B.evalT env input))) := rfl

@[circuit_norm]
theorem toSubcircuit_ProverSpec (impl : Impl B c) (s : B.State) (input : c.Input B.Var)
    (env : B.Cell → B.Native) :
    (impl.toSubcircuit s input).ProverSpec env =
      (c.inputCType.Valid (B.evalT env input) ∧ c.ProverAssumptions (c.inputCType.decode (B.evalT env input)) →
        (c.inputCType.Valid (B.evalT env input) ∧ c.Assumptions (c.inputCType.decode (B.evalT env input)) →
          c.outputCType.Valid (B.evalT env (impl.output input s)) ∧
            c.Spec (c.inputCType.decode (B.evalT env input)) (c.outputCType.decode (B.evalT env (impl.output input s)))) ∧
        c.outputCType.Valid (B.evalT env (impl.output input s)) ∧
          c.ProverSpec (c.inputCType.decode (B.evalT env input)) (c.outputCType.decode (B.evalT env (impl.output input s)))) := rfl

@[circuit_norm]
theorem toSubcircuit_pre (impl : Impl B c) (s : B.State) (input : c.Input B.Var) :
    (impl.toSubcircuit s input).pre = (B.footprintT input ⊆ B.Alloc s) := rfl

@[circuit_norm]
theorem toSubcircuit_post (impl : Impl B c) (s : B.State) (input : c.Input B.Var) :
    (impl.toSubcircuit s input).post =
      (B.footprintT (impl.output input s) ⊆ B.Alloc (impl.advance input s)) := rfl

/-! ### Witness generation, and the completeness statement it makes non-vacuous -/

/-- An honest environment exists on top of any assignment of the existing heap. -/
theorem honest_env_exists (impl : Impl B c) (input : c.Input B.Var) (s : B.State)
    (env₀ : B.Cell → B.Native) (h_in : B.footprintT input ⊆ B.Alloc s) :
    ∃ env, (∀ c ∈ B.Alloc s, env c = env₀ c) ∧ ((impl.main input).operations s).Honest env s :=
  Backend.flatHonest_exists _ s env₀
    (Ops.local_of_localHold (impl.consistent input s) (impl.spatial input s h_in)).1

/-- Completeness, as a statement about the real constraints: for inputs that exist in the heap
and satisfy the prover assumptions, some honest environment (agreeing with the given one on the
existing heap) satisfies all constraints, and the prover spec holds there. -/
theorem exists_honest_env (impl : Impl B c) (input : c.Input B.Var) (s : B.State)
    (env₀ : B.Cell → B.Native) (h_in : B.footprintT input ⊆ B.Alloc s)
    (h_prover : c.inputCType.Valid (B.evalT env₀ input) ∧ c.ProverAssumptions (c.inputCType.decode (B.evalT env₀ input))) :
    ∃ env, (∀ c ∈ B.Alloc s, env c = env₀ c) ∧
      ((impl.main input).operations s).ConstraintsHold env s ∧
      c.outputCType.Valid (B.evalT env (impl.output input s)) ∧
        c.ProverSpec (c.inputCType.decode (B.evalT env input)) (c.outputCType.decode (B.evalT env (impl.output input s))) := by
  obtain ⟨env, h_agree, h_honest⟩ := impl.honest_env_exists input s env₀ h_in
  have h_consistent := impl.consistent input s
  have h_prover' : c.inputCType.Valid (B.evalT env input) ∧ c.ProverAssumptions (c.inputCType.decode (B.evalT env input)) := by
    rwa [Backend.evalT_frame env env₀ input fun c hc => h_agree c (h_in hc)]
  have h := impl.completeness s env input (Ops.honestCompleteness_of_honest h_consistent h_honest) h_prover'
  exact ⟨env, h_agree, Ops.constraintsHold_of_completenessHold h_consistent h_honest h.1, h.2⟩

end Impl
end

/-! ### Refinement: an implementation of a stronger contract implements a weaker one -/

/-- `c.refine`: the same types, another contract. -/
abbrev Interface.refine {Native : Type} (c : Interface Native)
    (Assumptions : c.input → Prop) (Spec : c.input → c.output → Prop)
    (ProverAssumptions : c.input → Prop) (ProverSpec : c.input → c.output → Prop) :
    Interface Native :=
  { c with Assumptions, Spec, ProverAssumptions, ProverSpec }

/-- `c.Refines A S PA PS`: `c` assumes less and promises more than the contract `A S PA PS`. -/
structure Interface.Refines {Native : Type} (c : Interface Native)
    (Assumptions : c.input → Prop) (Spec : c.input → c.output → Prop)
    (ProverAssumptions : c.input → Prop) (ProverSpec : c.input → c.output → Prop) :
    Prop where
  assumptions : ∀ x, Assumptions x → c.Assumptions x
  spec : ∀ x y, Assumptions x → c.Spec x y → Spec x y
  proverAssumptions : ∀ x, ProverAssumptions x → c.ProverAssumptions x
  proverSpec : ∀ x y, ProverAssumptions x → c.ProverSpec x y → ProverSpec x y

def Impl.refine {B : Backend} {c : Interface B.Native} (impl : Impl B c)
    {Assumptions : c.input → Prop} {Spec : c.input → c.output → Prop}
    {ProverAssumptions : c.input → Prop} {ProverSpec : c.input → c.output → Prop}
    (h : c.Refines Assumptions Spec ProverAssumptions ProverSpec) :
    Impl B (c.refine Assumptions Spec ProverAssumptions ProverSpec) where
  main := impl.main
  advance := impl.advance
  output := impl.output
  advance_eq := impl.advance_eq
  output_eq := impl.output_eq
  consistent := impl.consistent
  spatial := impl.spatial
  soundness s env input h_assumptions h_holds :=
    let r := impl.soundness s env input ⟨h_assumptions.1, h.assumptions _ h_assumptions.2⟩ h_holds
    ⟨r.1, h.spec _ _ h_assumptions.2 r.2⟩
  completeness s env input h_honest h_prover :=
    let r := impl.completeness s env input h_honest ⟨h_prover.1, h.proverAssumptions _ h_prover.2⟩
    ⟨r.1, r.2.1, h.proverSpec _ _ h_prover.2 r.2.2⟩

end Clean2
