/-
Interfaces and implementations.

- An `Interface` is a semantic contract on values: assumptions and specs, for both the
  verifier side (soundness) and the prover side (completeness). It does not mention any
  backend, circuit, or heap.
- An `Impl B iface` is a circuit on backend `B` together with proofs that it meets `iface`,
  and a proof of the (uniform) spatial contract: given its inputs exist, it is well-formed and
  its outputs exist afterwards.
- `Impl.call` uses an implementation as a subcircuit: the parent only sees the interface.
-/
module

public import Clean2.Core.Circuit
public import Clean2.Core.Spatial

@[expose] public section

namespace Clean2

/-- A formal interface: the semantic contract of a circuit. -/
structure Interface (F : Type) (Input Output : TypeMap) where
  /-- assumed for soundness -/
  Assumptions : Input F → Prop := fun _ => True
  /-- proved by soundness -/
  Spec : Input F → Output F → Prop := fun _ _ => True
  /-- assumed for completeness ("what the honest prover guarantees about the inputs") -/
  ProverAssumptions : Input F → Prop := fun _ => True
  /-- proved by completeness ("what the honest prover knows about the output") -/
  ProverSpec : Input F → Output F → Prop := fun _ _ => True

section
variable {B : Backend} {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/-- Soundness of `main` against `iface`: under the assumptions, if the (proof-level) constraints
hold then the spec holds on the input and output. -/
@[circuit_norm]
def Soundness (B : Backend) (main : Input B.Var → Circuit B (Output B.Var))
    (output : Input B.Var → B.State → Output B.Var) (iface : Interface B.Native Input Output) : Prop :=
  ∀ (s : B.State) (env : B.Cell → B.Native) (input : Input B.Var),
    iface.Assumptions (B.evalT env input) →
    ((main input).operations s).SoundnessHold env s →
    iface.Spec (B.evalT env input) (B.evalT env (output input s))

/-- Completeness of `main` against `iface`: if the prover is honest and the prover assumptions
hold, then the (proof-level) constraints hold and the prover spec holds. -/
@[circuit_norm]
def Completeness (B : Backend) (main : Input B.Var → Circuit B (Output B.Var))
    (output : Input B.Var → B.State → Output B.Var) (iface : Interface B.Native Input Output) : Prop :=
  ∀ (s : B.State) (env : B.Cell → B.Native) (input : Input B.Var),
    ((main input).operations s).HonestCompleteness env s →
    iface.ProverAssumptions (B.evalT env input) →
    ((main input).operations s).CompletenessHold env s ∧
    iface.ProverSpec (B.evalT env input) (B.evalT env (output input s))

/-- The spatial contract, the same for every implementation:
`{inputs exist} main {well-formed ∗ outputs exist}`. -/
@[circuit_norm]
def Spatial (B : Backend) (main : Input B.Var → Circuit B (Output B.Var))
    (output : Input B.Var → B.State → Output B.Var) : Prop :=
  ∀ (input : Input B.Var) (s : B.State), B.footprintT input ⊆ B.Alloc s →
    ((main input).operations s).LocalHold s fun s' => B.footprintT (output input s) ⊆ B.Alloc s'

/-- An implementation of `iface` on backend `B`. -/
structure Impl (B : Backend) (iface : Interface B.Native Input Output) where
  main : Input B.Var → Circuit B (Output B.Var)
  /-- the allocation state after a call. Opaque to callers: no layout is visible here.
  Defaults to running the circuit; override to give it a closed form. -/
  advance : Input B.Var → B.State → B.State := fun input s => ((main input).operations s).advance s
  /-- the output, ideally in a form that does not require running `main` -/
  output : Input B.Var → B.State → Output B.Var := fun input s => (main input).output s
  advance_eq : ∀ input s, ((main input).operations s).advance s = advance input s := by
    intros; rfl
  output_eq : ∀ input s, (main input).output s = output input s := by
    intros; rfl
  consistent : ∀ input s, ((main input).operations s).Consistent s := by
    intros; simp only [circuit_norm]; try trivial
  spatial : Spatial B main output := by spatial
  soundness : Soundness B main output iface
  completeness : Completeness B main output iface

namespace Impl
variable {iface : Interface B.Native Input Output}

/-- The contract of `impl` at a call site. This is the theorem that lets a caller forget
the implementation. -/
def toSubcircuit (impl : Impl B iface) (s : B.State) (input : Input B.Var) : Subcircuit B s where
  ops := ((impl.main input).operations s).toFlat
  next := impl.advance input s
  next_eq := by rw [Ops.flatAdvance_toFlat (impl.consistent input s), impl.advance_eq]
  Assumptions env := iface.Assumptions (B.evalT env input)
  Spec env := iface.Spec (B.evalT env input) (B.evalT env (impl.output input s))
  ProverAssumptions env := iface.ProverAssumptions (B.evalT env input)
  ProverSpec env :=
    iface.ProverAssumptions (B.evalT env input) →
      (iface.Assumptions (B.evalT env input) →
        iface.Spec (B.evalT env input) (B.evalT env (impl.output input s))) ∧
      iface.ProverSpec (B.evalT env input) (B.evalT env (impl.output input s))
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
def call (impl : Impl B iface) (input : Input B.Var) : Circuit B (Output B.Var) :=
  fun s => (impl.output input s, [.call (impl.toSubcircuit s input)])

instance : CoeFun (Impl B iface) (fun _ => Input B.Var → Circuit B (Output B.Var)) := ⟨call⟩

/-! What a caller sees of a call, in each of the proof-level semantics.

Interfaces are plain definitions and are not in `circuit_norm`. A parent proof first runs
`simp only [circuit_norm]`, which turns each call into its interface's `Assumptions`/`Spec`
(etc.), and then unfolds the interfaces it uses in a second `simp only [circuit_norm, X.iface]`.
The two steps cannot be merged: `simp` unfolds `X.iface` by `dsimp` in the (dependent) `iface`
argument of `Impl.toSubcircuit` as well, after which `impl : Impl B X.iface` no longer matches
the lemmas below at reducible transparency, and the call is never taken apart. -/

@[circuit_norm]
theorem toSubcircuit_next (impl : Impl B iface) (s : B.State) (input : Input B.Var) :
    (impl.toSubcircuit s input).next = impl.advance input s := rfl

@[circuit_norm]
theorem toSubcircuit_Assumptions (impl : Impl B iface) (s : B.State) (input : Input B.Var) (env : B.Cell → B.Native) :
    (impl.toSubcircuit s input).Assumptions env = iface.Assumptions (B.evalT env input) := rfl

@[circuit_norm]
theorem toSubcircuit_Spec (impl : Impl B iface) (s : B.State) (input : Input B.Var) (env : B.Cell → B.Native) :
    (impl.toSubcircuit s input).Spec env =
      iface.Spec (B.evalT env input) (B.evalT env (impl.output input s)) := rfl

@[circuit_norm]
theorem toSubcircuit_ProverAssumptions (impl : Impl B iface) (s : B.State) (input : Input B.Var) (env : B.Cell → B.Native) :
    (impl.toSubcircuit s input).ProverAssumptions env = iface.ProverAssumptions (B.evalT env input) := rfl

@[circuit_norm]
theorem toSubcircuit_ProverSpec (impl : Impl B iface) (s : B.State) (input : Input B.Var) (env : B.Cell → B.Native) :
    (impl.toSubcircuit s input).ProverSpec env =
      (iface.ProverAssumptions (B.evalT env input) →
        (iface.Assumptions (B.evalT env input) →
          iface.Spec (B.evalT env input) (B.evalT env (impl.output input s))) ∧
        iface.ProverSpec (B.evalT env input) (B.evalT env (impl.output input s))) := rfl

@[circuit_norm]
theorem toSubcircuit_pre (impl : Impl B iface) (s : B.State) (input : Input B.Var) :
    (impl.toSubcircuit s input).pre = (B.footprintT input ⊆ B.Alloc s) := rfl

@[circuit_norm]
theorem toSubcircuit_post (impl : Impl B iface) (s : B.State) (input : Input B.Var) :
    (impl.toSubcircuit s input).post = (B.footprintT (impl.output input s) ⊆ B.Alloc (impl.advance input s)) := rfl

/-! ### Witness generation, and the completeness statement it makes non-vacuous -/

/-- An honest environment exists on top of any assignment of the existing heap. -/
theorem honest_env_exists (impl : Impl B iface) (input : Input B.Var) (s : B.State) (env₀ : B.Cell → B.Native)
    (h_in : B.footprintT input ⊆ B.Alloc s) :
    ∃ env, (∀ c ∈ B.Alloc s, env c = env₀ c) ∧ ((impl.main input).operations s).Honest env s :=
  Backend.flatHonest_exists _ s env₀
    (Ops.local_of_localHold (impl.consistent input s) (impl.spatial input s h_in)).1

/-- Completeness, as a statement about the real constraints: for inputs that exist in the heap
and satisfy the prover assumptions, some honest environment (agreeing with the given one on the
existing heap) satisfies all constraints, and the prover spec holds there. -/
theorem exists_honest_env (impl : Impl B iface) (input : Input B.Var) (s : B.State) (env₀ : B.Cell → B.Native)
    (h_in : B.footprintT input ⊆ B.Alloc s) (h_prover : iface.ProverAssumptions (B.evalT env₀ input)) :
    ∃ env, (∀ c ∈ B.Alloc s, env c = env₀ c) ∧
      ((impl.main input).operations s).ConstraintsHold env s ∧
      iface.ProverSpec (B.evalT env input) (B.evalT env (impl.output input s)) := by
  obtain ⟨env, h_agree, h_honest⟩ := impl.honest_env_exists input s env₀ h_in
  have h_consistent := impl.consistent input s
  have h_prover' : iface.ProverAssumptions (B.evalT env input) := by
    rwa [Backend.evalT_frame env env₀ input fun c hc => h_agree c (h_in hc)]
  have h := impl.completeness s env input (Ops.honestCompleteness_of_honest h_consistent h_honest) h_prover'
  exact ⟨env, h_agree, Ops.constraintsHold_of_completenessHold h_consistent h_honest h.1, h.2⟩

end Impl
end
end Clean2
