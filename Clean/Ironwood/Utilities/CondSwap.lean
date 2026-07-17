import Clean.Halo2
import Clean.Ironwood.Ecc.Basic
import Clean.Orchard.Specs.Pallas

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

namespace Halo2.Ironwood.CondSwap

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
def swapGate (cfg : Config) : Gate Fp where
  name := "a' = b ⋅ swap + a ⋅ (1-swap)"
  selector := cfg.qSwap
  constraints :=
    let a : Expression Fp Query := queryAdvice cfg.a 0
    let b : Expression Fp Query := queryAdvice cfg.b 0
    let aSwapped : Expression Fp Query := queryAdvice cfg.aSwapped 0
    let bSwapped : Expression Fp Query := queryAdvice cfg.bSwapped 0
    let swap : Expression Fp Query := queryAdvice cfg.swap 0
    let aCheck := aSwapped - (swap * b + ((1 : Fp) - swap) * a)
    let bCheck := bSwapped - (swap * a + ((1 : Fp) - swap) * b)
    let boolCheck := swap * ((1 : Fp) - swap)
    Constraints.withSelector cfg.qSwap
      [("a check", aCheck), ("b check", bCheck), ("swap is bool", boolCheck)]

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

end Halo2.Ironwood.CondSwap
