import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Poseidon.HashTheorems

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon/pow5.rs`
- `Pow5Config` (lines 21-35): the `WIDTH` state advices, the `partial_sbox` advice, the
  `rc_a`/`rc_b` fixed columns, and the three selectors `s_full`/`s_partial`/`s_pad_and_add`.
- `Pow5Chip::configure` (lines 56-202): equality on the state columns and `rc_b`
  ("scratch space" for fixed values), the three selectors, then the three gates
  `"full round"` (94-114), `"partial rounds"` (116-160), `"pad-and-add"` (162-186).

This port is specialized to Orchard's `P128Pow5T3` instance (`WIDTH = 3`, `RATE = 2`):
the MDS matrix and its inverse are baked into the gate polynomials as constants (as in
Rust, where `m_reg`/`m_inv` come from `S::constants()`), while the round constants live
in the `rc_a`/`rc_b` fixed columns and are queried by the gates.

The proof-content donor is `Clean/Orchard/Poseidon/` (`Pow5.lean`, `Sponge.lean`,
`Hash.lean`): `pow5`, `FullRound.value`, `PartialRounds.value` (+ the `mds`/`mdsInv`
inverse algebra), the `Permute.value` 4+28+4 schedule, and the sponge/hash value
composition are consumed directly from there.
-/

namespace Zcash.Circuits.Poseidon

open Halo2
open Poseidon (pow5)
open Poseidon.Permute (State)
open Poseidon.Permute.P128Pow5T3 (mds mdsInv)

/-- Rust `Pow5Config` (`pow5.rs:21-35`), width-3/rate-2: the three state advices, the
`partial_sbox` advice, the `rc_a`/`rc_b` fixed triples, and the three round selectors. -/
structure Config where
  state : Fin 3 → Column .advice
  partialSbox : Column .advice
  rcA : Fin 3 → Column .fixed
  rcB : Fin 3 → Column .fixed
  sFull : Selector
  sPartial : Selector
  sPadAndAdd : Selector

/-- Rust `pow_5` (`pow5.rs:89-92`): `v² · v² · v`, in the source's exact association. -/
@[selector_free, query_correct]
def pow5Expr (v : Expression Fp Query) : Expression Fp Query :=
  let v2 := v * v
  v2 * v2 * v

/-- Rust `"full round"` gate (`pow5.rs:94-114`): for each `next_idx`, the MDS row applied
to the S-boxed current state minus the next-row state. Term orientation is the source's
`pow_5(state_cur + rc_a) * m_reg[next_idx][idx]` (constant on the right), summed by
left-fold. -/
def fullRoundGate (cfg : Config) : Gate Fp :=
  -- Execution order: `state_next` for next_idx=0 registers first, then the inner idx-loop's
  -- cur/rc_a atoms (which dedup for the later next_idx), so `state[1]/[2] @ next` land last.
  Gate.withSelector "full round" cfg.sFull
    [ queryAdvice (cfg.state 0) 1, queryAdvice (cfg.state 0) 0, queryFixed (cfg.rcA 0),
      queryAdvice (cfg.state 1) 0, queryFixed (cfg.rcA 1),
      queryAdvice (cfg.state 2) 0, queryFixed (cfg.rcA 2),
      queryAdvice (cfg.state 1) 1, queryAdvice (cfg.state 2) 1 ] <|
    let term (nextIdx idx : Fin 3) : Expression Fp Query :=
      pow5Expr (queryAdvice (cfg.state idx) 0 + queryFixed (cfg.rcA idx))
        * (mds nextIdx idx : Fp)
    let row (nextIdx : Fin 3) : Expression Fp Query :=
      term nextIdx 0 + term nextIdx 1 + term nextIdx 2
        - queryAdvice (cfg.state nextIdx) 1
    [("", row 0), ("", row 1), ("", row 2)]

@[circuit_norm, synthesis_summary_norm]
theorem fullRoundGate_selector (cfg : Config) :
    (fullRoundGate cfg).selector = cfg.sFull := rfl

/-- Rust `"partial rounds"` gate (`pow5.rs:116-160`): the double-round row. `mid i` is the
MDS row over `(mid_0_sbox, cur₁ + rc_a₁, cur₂ + rc_a₂)`; `next i` is the `m_inv` row over
the next-row state; constraints are `state[0]` round a (S-box), `state[0]` round b, and the
two linear rounds — in the source's exact order and orientation. -/
def partialRoundsGate (cfg : Config) : Gate Fp :=
  -- Order: the four top lets (cur_0, mid_0, rc_a0, rc_b0), then `mid(0)`'s cur/rc_a atoms,
  -- then `next(0)`'s three next-row states, then rc_b[1], rc_b[2] from the linear rounds.
  Gate.withSelector "partial rounds" cfg.sPartial
    [ queryAdvice (cfg.state 0) 0, queryAdvice cfg.partialSbox 0,
      queryFixed (cfg.rcA 0), queryFixed (cfg.rcB 0),
      queryAdvice (cfg.state 1) 0, queryFixed (cfg.rcA 1),
      queryAdvice (cfg.state 2) 0, queryFixed (cfg.rcA 2),
      queryAdvice (cfg.state 0) 1, queryAdvice (cfg.state 1) 1, queryAdvice (cfg.state 2) 1,
      queryFixed (cfg.rcB 1), queryFixed (cfg.rcB 2) ] <|
    let cur (i : Fin 3) : Expression Fp Query := queryAdvice (cfg.state i) 0
    let rcA (i : Fin 3) : Expression Fp Query := queryFixed (cfg.rcA i)
    let rcB (i : Fin 3) : Expression Fp Query := queryFixed (cfg.rcB i)
    let mid0 : Expression Fp Query := queryAdvice cfg.partialSbox 0
    let mid (i : Fin 3) : Expression Fp Query :=
      mid0 * (mds i 0 : Fp)
        + (cur 1 + rcA 1) * (mds i 1 : Fp)
        + (cur 2 + rcA 2) * (mds i 2 : Fp)
    let nextQ (i : Fin 3) : Expression Fp Query := queryAdvice (cfg.state i) 1
    let next (i : Fin 3) : Expression Fp Query :=
      nextQ 0 * (mdsInv i 0 : Fp) + nextQ 1 * (mdsInv i 1 : Fp) + nextQ 2 * (mdsInv i 2 : Fp)
    [("", pow5Expr (cur 0 + rcA 0) - mid0),
     ("", pow5Expr (mid 0 + rcB 0) - next 0),
     ("", mid 1 + rcB 1 - next 1),
     ("", mid 2 + rcB 2 - next 2)]

@[circuit_norm, synthesis_summary_norm]
theorem partialRoundsGate_selector (cfg : Config) :
    (partialRoundsGate cfg).selector = cfg.sPartial := rfl

/-- Rust `"pad-and-add"` gate (`pow5.rs:162-186`): over rows `prev`/`cur`/`next`, each
rate word satisfies `initial + input - output`, and the capacity element is copied
through unchanged. -/
def padAndAddGate (cfg : Config) : Gate Fp :=
  -- Order: the rate (state[2]) prev/next lets first, then the pad_and_add loop over
  -- idx 0,1 (prev/cur/next each).
  Gate.withSelector "pad-and-add" cfg.sPadAndAdd
    [ queryAdvice (cfg.state 2) (-1), queryAdvice (cfg.state 2) 1,
      queryAdvice (cfg.state 0) (-1), queryAdvice (cfg.state 0) 0, queryAdvice (cfg.state 0) 1,
      queryAdvice (cfg.state 1) (-1), queryAdvice (cfg.state 1) 0, queryAdvice (cfg.state 1) 1 ] <|
    let padAndAdd (i : Fin 3) : Expression Fp Query :=
      queryAdvice (cfg.state i) (-1) + queryAdvice (cfg.state i) 0
        - queryAdvice (cfg.state i) 1
    [("", padAndAdd 0), ("", padAndAdd 1),
     ("", queryAdvice (cfg.state 2) (-1) - queryAdvice (cfg.state 2) 1)]

@[circuit_norm, synthesis_summary_norm]
theorem padAndAddGate_selector (cfg : Config) :
    (padAndAddGate cfg).selector = cfg.sPadAndAdd := rfl

@[reducible] def configureEqualities
    (state : Fin 3 → Column .advice) (rcB : Fin 3 → Column .fixed) :
    Configure Fp Unit := do
  enableEquality (state 0).toAny
  enableEquality (state 1).toAny
  enableEquality (state 2).toAny
  enableEquality (rcB 0).toAny
  enableEquality (rcB 1).toAny
  enableEquality (rcB 2).toAny

instance (state : Fin 3 → Column .advice)
    (rcB : Fin 3 → Column .fixed) :
    ElaboratedConfigure (configureEqualities state rcB) := by
  unfold configureEqualities
  infer_instance

@[reducible] def configureGates (cfg : Config) : Configure Fp Unit := do
  createGate (fullRoundGate cfg)
  createGate (partialRoundsGate cfg)
  createGate (padAndAddGate cfg)

instance (cfg : Config) : ElaboratedConfigure (configureGates cfg) := by
  unfold configureGates
  infer_instance

/-- Rust `Pow5Chip::configure` (`pow5.rs:56-202`), VK-exact: equality on the state
columns then `rc_b` (`pow5.rs:77-82`), the three selectors in allocation order, the
three gates in registration order. -/
def configure (state : Fin 3 → Column .advice) (partialSbox : Column .advice)
    (rcA rcB : Fin 3 → Column .fixed) : Configure Fp Config := do
  configureEqualities state rcB
  let sFull ← selector
  let sPartial ← selector
  let sPadAndAdd ← selector
  let cfg : Config := { state, partialSbox, rcA, rcB, sFull, sPartial, sPadAndAdd }
  configureGates cfg
  return cfg

/-- Every state column is equality-enabled by the Pow5 configure program. -/
theorem state_mem_configure_permutationRequests
    (state : Fin 3 → Column .advice) (partialSbox : Column .advice)
    (rcA rcB : Fin 3 → Column .fixed) (counts : ConfigureCounts) (i : Fin 3) :
    (state i).toAny ∈
      ((configure state partialSbox rcA rcB).delta counts).permutationRequests := by
  fin_cases i
  · unfold configure
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold configureEqualities
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _
  · unfold configure
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold configureEqualities
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _
  · unfold configure
    apply Configure.mem_permutationRequests_delta_bind_left
    unfold configureEqualities
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_right
    apply Configure.mem_permutationRequests_delta_bind_left
    exact Configure.mem_permutationRequests_delta_enableEquality _ _

@[reducible] def configureElaborated
    (state : Fin 3 → Column .advice) (partialSbox : Column .advice)
    (rcA rcB : Fin 3 → Column .fixed) :
    ElaboratedConfigure (configure state partialSbox rcA rcB) := by
  dsimp only [configure]
  infer_instance

instance (state : Fin 3 → Column .advice) (partialSbox : Column .advice)
    (rcA rcB : Fin 3 → Column .fixed) :
    ElaboratedConfigure (configure state partialSbox rcA rcB) :=
  { configureElaborated state partialSbox rcA rcB with
    selectorRequirements _ := True
    selectorsAllocated := by
      intro counts _
      constructor
      · simp [configure, configureEqualities, configureGates,
          fullRoundGate, partialRoundsGate, padAndAddGate,
          Gate.withSelector]
        omega
      · simp [configure, configureEqualities, configureGates,
          lookupInputSelectorBound] }

end Zcash.Circuits.Poseidon
