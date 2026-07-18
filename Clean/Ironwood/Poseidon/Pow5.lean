import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Ironwood.Ecc.Basic
import Clean.Orchard.Poseidon.Hash

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

namespace Halo2.Ironwood.Poseidon

open Halo2.Ironwood (Fp)
open Orchard.Poseidon (pow5)
open Orchard.Poseidon.Permute (State)
open Orchard.Poseidon.Permute.P128Pow5T3 (mds mdsInv)

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
def pow5Expr (v : Expression Fp Query) : Expression Fp Query :=
  let v2 := v * v
  v2 * v2 * v

/-- Rust `"full round"` gate (`pow5.rs:94-114`): for each `next_idx`, the MDS row applied
to the S-boxed current state minus the next-row state. Term orientation is the source's
`pow_5(state_cur + rc_a) * m_reg[next_idx][idx]` (constant on the right), summed by
left-fold. -/
def fullRoundGate (cfg : Config) : Gate Fp where
  name := "full round"
  selector := cfg.sFull
  constraints :=
    let term (nextIdx idx : Fin 3) : Expression Fp Query :=
      pow5Expr (queryAdvice (cfg.state idx) 0 + queryFixed (cfg.rcA idx))
        * (mds nextIdx idx : Fp)
    let row (nextIdx : Fin 3) : Expression Fp Query :=
      term nextIdx 0 + term nextIdx 1 + term nextIdx 2
        - queryAdvice (cfg.state nextIdx) 1
    Constraints.withSelector cfg.sFull
      [("", row 0), ("", row 1), ("", row 2)]

/-- Rust `"partial rounds"` gate (`pow5.rs:116-160`): the double-round row. `mid i` is the
MDS row over `(mid_0_sbox, cur₁ + rc_a₁, cur₂ + rc_a₂)`; `next i` is the `m_inv` row over
the next-row state; constraints are `state[0]` round a (S-box), `state[0]` round b, and the
two linear rounds — in the source's exact order and orientation. -/
def partialRoundsGate (cfg : Config) : Gate Fp where
  name := "partial rounds"
  selector := cfg.sPartial
  constraints :=
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
    Constraints.withSelector cfg.sPartial
      [("", pow5Expr (cur 0 + rcA 0) - mid0),
       ("", pow5Expr (mid 0 + rcB 0) - next 0),
       ("", mid 1 + rcB 1 - next 1),
       ("", mid 2 + rcB 2 - next 2)]

/-- Rust `"pad-and-add"` gate (`pow5.rs:162-186`): over rows `prev`/`cur`/`next`, each
rate word satisfies `initial + input - output`, and the capacity element is copied
through unchanged. -/
def padAndAddGate (cfg : Config) : Gate Fp where
  name := "pad-and-add"
  selector := cfg.sPadAndAdd
  constraints :=
    let padAndAdd (i : Fin 3) : Expression Fp Query :=
      queryAdvice (cfg.state i) (-1) + queryAdvice (cfg.state i) 0
        - queryAdvice (cfg.state i) 1
    Constraints.withSelector cfg.sPadAndAdd
      [("", padAndAdd 0), ("", padAndAdd 1),
       ("", queryAdvice (cfg.state 2) (-1) - queryAdvice (cfg.state 2) 1)]

/-- Rust `Pow5Chip::configure` (`pow5.rs:56-202`), VK-exact: equality on the state
columns then `rc_b` (`pow5.rs:77-82`), the three selectors in allocation order, the
three gates in registration order. -/
def configure (state : Fin 3 → Column .advice) (partialSbox : Column .advice)
    (rcA rcB : Fin 3 → Column .fixed) : Configure Fp Config := do
  enableEquality (state 0).toAny
  enableEquality (state 1).toAny
  enableEquality (state 2).toAny
  enableEquality (rcB 0).toAny
  enableEquality (rcB 1).toAny
  enableEquality (rcB 2).toAny
  let sFull ← selector
  let sPartial ← selector
  let sPadAndAdd ← selector
  let cfg : Config := { state, partialSbox, rcA, rcB, sFull, sPartial, sPadAndAdd }
  createGate (fullRoundGate cfg)
  createGate (partialRoundsGate cfg)
  createGate (padAndAddGate cfg)
  return cfg

end Halo2.Ironwood.Poseidon
