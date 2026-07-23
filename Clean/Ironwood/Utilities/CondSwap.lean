import Clean.Halo2
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Specs.Pallas

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/cond_swap.rs`
- `CondSwapConfig` (lines 41-49)
- `CondSwapChip::configure` (lines 235-287)
- `CondSwapInstructions::swap` (lines 100-160)

The conditional-swap chip: given a pair `(a, b)` and a boolean `swap`, witness
`(a', b') = if swap then (b, a) else (a, b)`. One row, five advice columns, one simple
selector, one gate with three constraints (`a_check`, `b_check`, `swap is bool` — the
Rust `ternary`/`bool_check` helpers, `utilities.rs:133-143`).

This file carries the VK-facing surface (`Config`, the gate, `configure` — Rust-exact in
registration order, used by `MerkleChip::configure`); the `swap` gadget bundle follows the
`MulOverflow`-style leaf pattern. Phase-one donor: `Clean/Orchard/Utilities.lean`,
namespace `CondSwap`.
-/

namespace Zcash.Circuits.CondSwap

open Halo2

/-- Rust `CondSwapConfig` (`cond_swap.rs:41-49`): the simple `q_swap` selector and the five
advice columns `a, b, a_swapped, b_swapped, swap` (Merkle instantiates them with the five
Sinsemilla hash advices). -/
structure Config where
  qSwap : Selector
  a : Column .advice
  b : Column .advice
  aSwapped : Column .advice
  bSwapped : Column .advice
  swap : Column .advice

/-- Rust `"a' = b ⋅ swap + a ⋅ (1-swap)"` gate (`cond_swap.rs:256-284`), gated by `q_swap`,
all cells at `Rotation::cur`. Three constraints, with the Rust `ternary(a,b,c) =
a·b + (1−a)·c` and `bool_check(v) = v·(1−v)` ASTs verbatim:

- `a_check`: `a_swapped − (swap·b + (1−swap)·a)`
- `b_check`: `b_swapped − (swap·a + (1−swap)·b)`
- `swap is bool`: `swap·(1−swap)` -/
def swapGate (cfg : Config) : Gate Fp :=
  let a : Expression Fp Query := queryAdvice cfg.a 0
  let b : Expression Fp Query := queryAdvice cfg.b 0
  let aSwapped : Expression Fp Query := queryAdvice cfg.aSwapped 0
  let bSwapped : Expression Fp Query := queryAdvice cfg.bSwapped 0
  let swap : Expression Fp Query := queryAdvice cfg.swap 0
  let aCheck := aSwapped - (swap * b + ((1 : Fp) - swap) * a)
  let bCheck := bSwapped - (swap * a + ((1 : Fp) - swap) * b)
  let boolCheck := swap * ((1 : Fp) - swap)
  { name := "a' = b ⋅ swap + a ⋅ (1-swap)"
    selector := cfg.qSwap
    queriedCells := [a, b, aSwapped, bSwapped, swap]
    constraints := Constraints.withSelector cfg.qSwap
      [("a check", aCheck), ("b check", bCheck), ("swap is bool", boolCheck)] }

/-- Rust `CondSwapChip::configure` (`cond_swap.rs:235-287`), VK-exact: equality on column
`a` only (`cond_swap.rs:241` — the other columns are the caller's business), the simple
`q_swap` selector, the swap gate. -/
def configure (a b aSwapped bSwapped swap : Column .advice) : Configure Fp Config := do
  -- cond_swap.rs:241 — only column `a` is equality-enabled by this chip
  enableEquality a.toAny
  let qSwap ← selector
  let cfg : Config := { qSwap, a, b, aSwapped, bSwapped, swap }
  createGate (swapGate cfg)
  return cfg

/-! ## The `swap` gadget (Rust `CondSwapInstructions::swap`, `cond_swap.rs:88-134`)

One row: copy `a` in, witness `b` and the boolean `swap` flag, witness the conditionally
swapped pair, enable the gate. The `swap` witness program is `Bool`-valued (Rust:
`Value<bool>`), so the honest run is boolean by construction. -/

/-- The `a` input (the cell copied in). -/
structure Input (F : Type) where
  a : F
deriving ProvableStruct

/-- The swapped pair. -/
structure Output (F : Type) where
  aSwapped : F
  bSwapped : F
deriving ProvableStruct

/-- The verifier-view swap contract over the pair `(b, swap)` of witnessed values:
`swap` is boolean and the output pair is the (conditionally) swapped `(a, b)`. -/
def SwapSpec (a : Fp) (output : Output Fp) (wit : Fp × Fp) : Prop :=
  IsBool wit.2 ∧
  output.aSwapped = (if wit.2 = 1 then wit.1 else a) ∧
  output.bSwapped = (if wit.2 = 1 then a else wit.1)

/-- Rust `CondSwapChip::swap`'s region body as a formal circuit: input `a` (copied in),
parameterized by the `b` witness program and the `Bool`-valued `swap` program. Output
`(a_swapped, b_swapped)`. -/
def swap (wb : WitgenIR Fp 1) (wswap : Placed ProverEnvironment Fp → Bool) :
    FormalRegionCircuit Fp Config Config Input Output where
  configure := pure

  synthesize cfg offset (input : Input (AssignedCell Fp)) := do
    -- cond_swap.rs:97 — q_swap first
    (swapGate cfg).enable offset
    let aC ← copyAdvice input.a cfg.a offset
    let b ← assignAdvice cfg.b offset wb
    let sw ← assignAdvice cfg.swap offset
      (.native fun env => #v[if wswap env then (1 : Fp) else 0])
    let aS ← assignAdvice cfg.aSwapped offset
      (.ofFExpr ((.expr sw) * (.expr b) + ((.const (1 : Fp)) - (.expr sw)) * (.expr aC)))
    let bS ← assignAdvice cfg.bSwapped offset
      (.ofFExpr ((.expr sw) * (.expr aC) + ((.const (1 : Fp)) - (.expr sw)) * (.expr b)))
    return { aSwapped := aS, bSwapped := bS }

  -- the `(b, swap)` cell values, as extraction data
  Witness := fieldPair
  extract cfg offset _ self env :=
    (eval env (AssignedCell.of self offset cfg.b : Var field Fp),
     eval env (AssignedCell.of self offset cfg.swap : Var field Fp))

  Spec := fun input output wit => SwapSpec input.a output wit

  ProverSpec := fun input output wit _ =>
    output.aSwapped = (if wit.2 = 1 then wit.1 else input.a) ∧
    output.bSwapped = (if wit.2 = 1 then input.a else wit.1)

  soundness := by
    circuit_proof_start [swapGate, SwapSpec]
    obtain ⟨⟨hACheck, hBCheck, hBool⟩, hCopy⟩ := hc
    set sw := env.advice cfg.swap ↑(place self + offset) with hsw
    have hboolv : IsBool sw := by
      rcases mul_eq_zero.mp hBool with h | h
      · exact Or.inl h
      · exact Or.inr (by linear_combination -h)
    refine ⟨hboolv, ?_, ?_⟩
    · rcases hboolv with h0 | h1
      · rw [if_neg (show ¬ sw = 1 from by rw [h0]; decide)]
        rw [h0] at hACheck
        linear_combination hACheck + hCopy
      · rw [if_pos h1]
        rw [h1] at hACheck
        linear_combination hACheck
    · rcases hboolv with h0 | h1
      · rw [if_neg (show ¬ sw = 1 from by rw [h0]; decide)]
        rw [h0] at hBCheck
        linear_combination hBCheck
      · rw [if_pos h1]
        rw [h1] at hBCheck
        linear_combination hBCheck + hCopy

  completeness := by
    circuit_proof_start [swapGate]
    obtain ⟨hOA, hOB⟩ := h_output
    rcases Bool.eq_false_or_eq_true (wswap { place := place, env := env }) with hs | hs <;>
      simp only [hs, Bool.false_eq_true, if_false, if_true] at hOA hOB ⊢
    · refine ⟨⟨by ring, by ring, by norm_num⟩, ?_, ?_⟩
      · linear_combination -hOA
      · linear_combination -hOB
    · refine ⟨⟨by ring, by ring, by norm_num⟩, ?_, ?_⟩
      · rw [if_neg (show ¬ (0 : Fp) = 1 from by decide)]
        linear_combination -hOA
      · rw [if_neg (show ¬ (0 : Fp) = 1 from by decide)]
        linear_combination -hOB

end Zcash.Circuits.CondSwap
