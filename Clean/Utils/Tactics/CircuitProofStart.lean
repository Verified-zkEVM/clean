import Lean
import Clean.Circuit.Basic
import Clean.Circuit.RawCircuit
import Clean.Utils.Tactics.ProvableStructSimp
import Clean.Utils.Tactics.SubcircuitNorm

open Lean Elab Tactic Meta
open Circuit

/--
  Introduce all standard parameters and hypotheses for Soundness or Completeness.
-/
partial def circuitProofStartCore : TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    let goalType ← goal.getType

    -- First check if this is a Soundness or Completeness type that needs unfolding
    -- We need to check the head constant of the expression
    let headConst? := goalType.getAppFn.constName?
    let isSoundness := headConst? == some ``Soundness ||
                       headConst? == some ``FormalAssertion.Soundness ||
                       headConst? == some ``GeneralFormalCircuit.Soundness
    let isRawSoundness := headConst? == some ``RawSoundness
    let isCompleteness := headConst? == some ``Completeness ||
                          headConst? == some ``FormalAssertion.Completeness ||
                          headConst? == some ``GeneralFormalCircuit.Completeness

    if isSoundness then
      match headConst? with
      | some ``Soundness =>
        evalTactic (← `(tactic| unfold Soundness))
        let names := [`i₀, `env, `input_var, `input, `h_input, `h_assumptions, `h_holds]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | some ``FormalAssertion.Soundness =>
        evalTactic (← `(tactic| unfold FormalAssertion.Soundness))
        let names := [`i₀, `env, `input_var, `input, `h_input, `h_assumptions, `h_holds]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | some ``GeneralFormalCircuit.Soundness =>
        evalTactic (← `(tactic| unfold GeneralFormalCircuit.Soundness))
        let names := [`i₀, `env, `input_var, `input, `h_input, `h_assumptions, `h_holds]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | _ => pure ()
      return
    else if isRawSoundness then
      evalTactic (← `(tactic| unfold RawSoundness))
      let names := [`i₀, `env, `input_var, `input, `h_input, `h_assumptions, `h_holds]
      for name in names do
        evalTactic (← `(tactic| intro $(mkIdent name):ident))
      return
    else if isCompleteness then
      -- Unfold the appropriate Completeness definition and introduce the correct parameters
      match headConst? with
      | some ``Completeness =>
        evalTactic (← `(tactic| unfold Completeness))
        let names := [`i₀, `env, `input_var, `h_env, `input, `h_input, `h_assumptions]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | some ``FormalAssertion.Completeness =>
        evalTactic (← `(tactic| unfold FormalAssertion.Completeness))
        let names := [`i₀, `env, `input_var, `h_env, `input, `h_input, `h_assumptions, `h_spec]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | some ``GeneralFormalCircuit.Completeness =>
        evalTactic (← `(tactic| unfold GeneralFormalCircuit.Completeness))
        let names := [`i₀, `env, `input_var, `h_env, `input, `h_input, `h_assumptions]
        for name in names do
          evalTactic (← `(tactic| intro $(mkIdent name):ident))
      | _ => pure ()
      return
    else
      -- Goal is not a supported Soundness or Completeness type
      throwError "circuit_proof_start can only be used on Soundness, Completeness, RawSoundness and variants"

/--
  Standard tactic for starting soundness and completeness proofs.

  This tactic:
  1. Automatically introduces all parameters for `Soundness` or `Completeness` goals
  2. Unfolds `main`, `Assumptions`, and `Spec` definitions
  3. Normalizes the goal state using circuit_norm
  4. Applies provable_struct_simp to decompose structs and decompose eval that mention struct components
  5. Additionally simplifies h_holds henv and the goal with circuit_norm and h_input

  **Supported goal types**: This tactic works on `Soundness`, `Completeness`,
  `FormalAssertion.Soundness`, `FormalAssertion.Completeness`,
  `GeneralFormalCircuit.Soundness`, `GeneralFormalCircuit.Completeness`, or `RawSoundness`.

  For `RawSoundness` goals, use `circuit_proof_start_raw` (which also runs `subcircuit_norm`)
  or `circuit_proof_all_raw` (which also closes the goal with `simp_all`) instead.

  **Optional argument**: You can provide additional lemmas for simplification by using square brackets:
  `circuit_proof_start [lemma1, lemma2, ...]`. These lemmas will be used alongside `circuit_norm`
  to simplify the goal and the hypotheses.

  Example usage:
  ```lean
  theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
    circuit_proof_start
    -- The assumptions in Soundness are introduced. All provable structs are decomposed when their components are mentioned

  theorem soundness_with_lemmas : Soundness (F p) elaborated Assumptions Spec := by
    circuit_proof_start [my_custom_lemma, another_lemma]
    -- Same as above but also uses my_custom_lemma and another_lemma in simplifications

  theorem completeness : Completeness (F p) elaborated Assumptions := by
    circuit_proof_start
    -- The assumptions in Completeness are introduced. All provable structs are decomposed when their components are mentioned
  ```
-/
syntax "circuit_proof_start" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| circuit_proof_start $[[$terms:term,*]]?) => do
  -- intro all hypotheses
  circuitProofStartCore

  -- try to unfold main, Assumptions and Spec as local definitions
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `Assumptions):ident] at *))
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `Spec):ident] at *))
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `elaborated):ident] at *)) -- sometimes `main` is hidden behind `elaborated`
  evalTactic (← `(tactic| try dsimp only [$(mkIdent `main):ident] at *))

  -- simplify structs / eval first
  try (evalTactic (← `(tactic| provable_struct_simp))) catch _ => pure ()

  -- Additional simplification for common patterns in soundness/completeness proofs
  -- Convert optional terms to simpLemma syntax
  let extraLemmas := match terms with
    | some terms => terms.getElems.map fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    | none => #[]
  let lemmasArray ← extraLemmas.mapM id

  try (evalTactic (← `(tactic| simp only [circuit_norm, $lemmasArray,*] at $(mkIdent `h_input):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm, $lemmasArray,*] at $(mkIdent `h_assumptions):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm, $(mkIdent `h_input):ident, $lemmasArray,*] at $(mkIdent `h_holds):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm, $(mkIdent `h_input):ident, $lemmasArray,*] at $(mkIdent `h_env):ident))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm, $(mkIdent `h_input):ident, $lemmasArray,*]))) catch _ => pure ()
  try (evalTactic (← `(tactic| simp only [circuit_norm, $lemmasArray,*] at $(mkIdent `h_spec):ident))) catch _ => pure ()

-- core version only, for experimentation with variants of this tactic
elab "circuit_proof_start_core" : tactic => do
  circuitProofStartCore

/--
  Tactic for starting `RawSoundness` proofs — the alternative proof pipeline using
  `subcircuit_norm` instead of the built-in `ConstraintsHold.Soundness` simplification.

  This tactic extends `circuit_proof_start` with two extra steps after expanding `h_holds`:

  1. `subcircuit_norm` — attempts to transform any `ConstraintsHoldFlat env s.ops.toFlat`
     hypothesis directly into `s.Spec env`.  This is a no-op when `h_holds` is a
     conjunction (the `ConstraintsHoldFlat` term is buried inside), so for circuits like
     `Addition8FullCarry` the user must `obtain` the parts first and then call
     `subcircuit_norm` manually.  For circuits with a **single** subcircuit call this step
     fires automatically (e.g. `Addition8Full`, `Addition8`).

  2. A second `simp [circuit_norm, ...]` on `h_holds` — simplifies any `s.Spec env`
     implication introduced by step 1 into its concrete `Assumptions → circuit.Spec` form.

  **Workflow** (for a circuit with a single subcircuit):

  ```
  circuit_proof_start_raw [Addition8FullCarry.circuit, ...]
    step 1 (circuit_proof_start):
      h_holds = ConstraintsHoldFlat env (Addition8FullCarry.circuit.toSubcircuit n x).ops.toFlat
    step 2 (subcircuit_norm fires):
      h_holds = (Addition8FullCarry.circuit.toSubcircuit n x).Spec env
    step 3 (second simp [circuit_norm, ...]):
      h_holds = Addition8FullCarry.Assumptions inputs → Addition8FullCarry.Spec inputs output
  ```

  For circuits with **multiple** subcircuits / assertions (like `Addition8FullCarry`), steps 2 and 3
  are no-ops on the unsplit conjunction. The user manually does:
  ```lean
  obtain ⟨h_byte, h_bool_raw, h_add⟩ := h_holds
  subcircuit_norm   -- now acts on h_bool_raw
  simp [circuit_norm] at h_bool_raw
  ```

  **`circuit_proof_all_raw`** is a one-shot version that also runs `simp_all` after these
  steps, closing the goal completely for circuits whose soundness follows directly.

  **Supported goal types**: `RawSoundness` only. Use `circuit_proof_start` for all other goal types.
-/
syntax "circuit_proof_start_raw" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| circuit_proof_start_raw $[[$terms:term,*]]?) => do
  let lemmas := terms.getD (.mk #[])
  -- Step 1: all normal circuit_proof_start steps (introduces parameters, simp on h_holds, etc.)
  evalTactic (← `(tactic| circuit_proof_start [$lemmas,*]))
  -- Step 2: apply subcircuit_norm — transforms ConstraintsHoldFlat → Spec when h_holds is
  -- a direct ConstraintsHoldFlat term (fires for single-subcircuit circuits).
  evalTactic (← `(tactic| try subcircuit_norm))
  -- Step 3: simplify any Spec implications that subcircuit_norm introduced
  let extraLemmas := match terms with
    | some ts => ts.getElems.map fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    | none => #[]
  let lemmasArray ← extraLemmas.mapM id
  try (evalTactic (← `(tactic| simp only [circuit_norm, $(mkIdent `h_input):ident, $lemmasArray,*] at $(mkIdent `h_holds):ident))) catch _ => pure ()

/--
  One-shot tactic for `RawSoundness` proofs whose correctness follows immediately from the
  subcircuit specs after normalisation.

  Equivalent to:
  ```lean
  circuit_proof_start_raw [lemmas...]   -- intro + expand + subcircuit_norm + second simp
  simp_all                              -- close by combining h_holds with h_assumptions
  ```

  Works out of the box for circuits that wrap a **single** subcircuit (e.g. `Addition8Full`,
  `Addition8`).  For circuits with multiple operations the user needs to `obtain`/split
  `h_holds` manually before the `simp_all` step can close the goal.

  **Example**:
  ```lean
  -- Raw analogue of Addition8Full, proved in one tactic:
  soundness := by
    circuit_proof_all_raw [Addition8FullCarry.circuit, Addition8FullCarry.Assumptions,
                            Addition8FullCarry.Spec]
  ```
-/
syntax "circuit_proof_all_raw" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| circuit_proof_all_raw $[[$terms:term,*]]?) => do
  let lemmas := terms.getD (.mk #[])
  evalTactic (← `(tactic| circuit_proof_start_raw [$lemmas,*]))
  evalTactic (← `(tactic| try simp_all))
  evalTactic (← `(tactic| done))

-- version of circuit_proof_start that attempts to close the goal with `simp_all`
syntax "circuit_proof_all" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| circuit_proof_all $[[$terms:term,*]]?) => do
  let lemmas := terms.getD (.mk #[])
  evalTactic (← `(tactic| circuit_proof_start [$lemmas,*]))
  evalTactic (← `(tactic| try simp_all))
  evalTactic (← `(tactic| done))
