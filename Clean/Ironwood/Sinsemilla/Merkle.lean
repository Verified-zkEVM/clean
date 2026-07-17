import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Specs.Sinsemilla
import Clean.Orchard.Specs.Bitrange
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Sinsemilla.Basic
import Clean.Ironwood.Sinsemilla.HashPiece
import Clean.Ironwood.Sinsemilla.Chain
import Clean.Ironwood.Utilities.LookupRangeCheck
import Clean.Ironwood.Utilities.CondSwap

/-!
# Sinsemilla MerkleCRH (Ironwood)

Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/merkle/chip.rs`
- `MerkleInstructions::hash_layer` (`chip.rs:225-380`) and the `Decomposition check`
  gate (`chip.rs:136-207`).

`MerkleCRH^Orchard(l, left, right) = SinsemillaHash(Q, l⋆ || left⋆ || right⋆)`: the 520-bit
message is witnessed as three Sinsemilla pieces
- `a = a_0 || a_1` = `l` (10 bits) `||` bits 0..240 of `left` (25 words),
- `b = b_0 || b_1 || b_2` = bits 240..250 of `left` `||` bits 250..255 of `left` `||`
  bits 0..5 of `right` (2 words),
- `c` = bits 5..255 of `right` (25 words),
with the short sub-pieces `b_1`, `b_2` witnessed separately and range-checked to 5 bits. The
`q_decompose` gate (`Merkle.Gate`, the `Decomposition check`) ties the pieces to `(l, left,
right)` through the hash's own `z_1` running-sum cells.

## Slice-3 scope / port map

- **Pure value algebra** (`Gate.Spec`-supporting digit toolkit, `merkleChunks_eq`, `assemble`,
  `honest_*`) is framework-agnostic (`Fp`/`ℕ`/shared spec-layer `merkleChunks`/`bitrange`), lifted
  **verbatim** from the donor `Clean/Orchard/Sinsemilla/Merkle.lean`. Names kept identical.
- **`Gate`** (`Decomposition check`, `q_decompose`) — ported as a region-level `createGate` +
  enable pure-assertion `FormalRegionCircuit` (the `MulOverflow.overflowGate` pattern), fully
  proven both directions.
- **`HashLayer`** composes the ported `Chain.circuit` (the hash; `z_1` cells read off its exposed
  `zs` HVec as `zs[i][1]`) + the ported `LookupRangeCheck.shortRangeCheck` (b_1/b_2 range checks)
  + the `Gate`. Structure-complete; the value glue is the lifted `assemble`/`honest_*`.
- **`Layer`** composes `CondSwap.Swap` + `HashLayer`. **`CondSwap` is NOT ported to the Ironwood
  region tree** (only the phase-one `Orchard.Utilities.CondSwap` exists) → the swap is a **stated
  boundary** (abstract child, cut line explicit), exactly as `MulFixed` is for `CommitDomain`.
- **`CalculateRoot`** is the 32-layer fold of `Layer`. Structure + the `MerkleRoot`/`MerkleStep`
  value algebra (`merkleRoot_of_steps`, `honestNode`) lifted; the per-layer composition rides on
  `Layer`.
-/

namespace Halo2.Ironwood.Sinsemilla.Merkle

open Orchard (Point)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Orchard.Specs.Sinsemilla (Generators merkleChunks hashToPoint)
open Orchard.Specs (K bitrange bitrange_lt bitrange_zero bitrange_eq_div_of_lt)
open Halo2.Ironwood.Sinsemilla (pieceWord pieceZ)

/-! ### MerkleCRH decomposition gate constants -/

def twoPow5 {R : Type} [OfNat R (2 ^ 5)] : R := OfNat.ofNat (2 ^ 5)
def twoPow10 {R : Type} [OfNat R (2 ^ 10)] : R := OfNat.ofNat (2 ^ 10)
def twoPow240 {R : Type} [OfNat R (2 ^ 240)] : R := OfNat.ofNat (2 ^ 240)

/-! ### The `q_decompose` gate (`chip.rs:136-207`)

Layout relative to the gate row `g` (`q_decompose` enabled at `Rotation::cur`):

    |  a   |  b   |  c   | left | right | q_decompose |   (row g)
    | z1_a | z1_b | b_1  | b_2  |   l   |      0      |   (row g+1)

`a_whole/b_whole/c_whole/left_node/right_node` are read at `Rotation::cur`, and
`z1_a/z1_b/b_1/b_2/l` at `Rotation::next`. -/

namespace Gate

/-- The Rust `q_decompose` config: the selector and the ten advice columns the gate reads across
the two rows. -/
structure Config where
  qDecompose : Selector
  aWhole : Column .advice
  bWhole : Column .advice
  cWhole : Column .advice
  leftNode : Column .advice
  rightNode : Column .advice
  z1A : Column .advice
  z1B : Column .advice
  b1 : Column .advice
  b2 : Column .advice
  lWhole : Column .advice

/-- The four decomposition polynomials (`chip.rs:159-193`), verbatim. `a_whole/…/right_node` at
`Rotation::cur`, `z1_a/z1_b/b_1/b_2/l` at `Rotation::next`.
- `l_check`   : `a_0 − l = (a_whole − z1_a·2^10) − l`
- `left_check`: `z1_a + (b_0 + b_1·2^10)·2^240 − left`, with `b_0 = b_whole − z1_b·2^10`
- `right_check`: `b_2 + c_whole·2^5 − right`
- `b1_b2_check`: `z1_b − (b_1 + b_2·2^5)` -/
def decomposeGate (cfg : Config) : Gate Fp where
  name := "Decomposition check"
  selector := cfg.qDecompose
  constraints :=
    let aWhole : Expression Fp Query := queryAdvice cfg.aWhole 0
    let bWhole : Expression Fp Query := queryAdvice cfg.bWhole 0
    let cWhole : Expression Fp Query := queryAdvice cfg.cWhole 0
    let leftNode : Expression Fp Query := queryAdvice cfg.leftNode 0
    let rightNode : Expression Fp Query := queryAdvice cfg.rightNode 0
    let z1A : Expression Fp Query := queryAdvice cfg.z1A 1
    let z1B : Expression Fp Query := queryAdvice cfg.z1B 1
    let b1 : Expression Fp Query := queryAdvice cfg.b1 1
    let b2 : Expression Fp Query := queryAdvice cfg.b2 1
    let l : Expression Fp Query := queryAdvice cfg.lWhole 1
    let twoPow5 : Expression Fp Query := (2 ^ 5 : Fp)
    let twoPow10 : Expression Fp Query := (2 ^ 10 : Fp)
    let twoPow240 : Expression Fp Query := (2 ^ 240 : Fp)
    let a0 := aWhole - z1A * twoPow10
    let b0 := bWhole - z1B * twoPow10
    let lCheck := a0 - l
    let leftCheck := z1A + (b0 + b1 * twoPow10) * twoPow240 - leftNode
    let rightCheck := b2 + cWhole * twoPow5 - rightNode
    let b1b2Check := z1B - (b1 + b2 * twoPow5)
    Constraints.withSelector cfg.qDecompose
      [ ("l_check", lCheck), ("left_check", leftCheck),
        ("right_check", rightCheck), ("b1_b2_check", b1b2Check) ]

/-- The value-level decomposition spec (donor `Merkle.Gate.Spec`), over the ten cell values.
Uses the plain `(2^k : Fp)` literals (definitionally the `twoPow*` constants). -/
def Spec (aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole : Fp) : Prop :=
  lWhole = aWhole - z1A * (2 ^ 10 : Fp) ∧
  leftNode = z1A + ((bWhole - z1B * (2 ^ 10 : Fp)) + b1 * (2 ^ 10 : Fp)) * (2 ^ 240 : Fp) ∧
  rightNode = b2 + cWhole * (2 ^ 5 : Fp) ∧
  z1B = b1 + b2 * (2 ^ 5 : Fp)

/-- Soundness half of the gate: the four polynomials vanishing gives the `Spec`. -/
theorem spec_of_polysZero {aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole : Fp}
    (hl : (aWhole - z1A * (2 ^ 10 : Fp)) - lWhole = 0)
    (hleft : z1A + ((bWhole - z1B * (2 ^ 10 : Fp)) + b1 * (2 ^ 10 : Fp)) * (2 ^ 240 : Fp)
      - leftNode = 0)
    (hright : b2 + cWhole * (2 ^ 5 : Fp) - rightNode = 0)
    (hb : z1B - (b1 + b2 * (2 ^ 5 : Fp)) = 0) :
    Spec aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -hl
  · linear_combination -hleft
  · linear_combination -hright
  · linear_combination hb

/-- Completeness half: the `Spec` gives each of the four polynomials vanishing (gate order). -/
theorem polysZero_of_spec {aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole : Fp}
    (h : Spec aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole) :
    (aWhole - z1A * (2 ^ 10 : Fp)) - lWhole = 0 ∧
    z1A + ((bWhole - z1B * (2 ^ 10 : Fp)) + b1 * (2 ^ 10 : Fp)) * (2 ^ 240 : Fp) - leftNode = 0 ∧
    b2 + cWhole * (2 ^ 5 : Fp) - rightNode = 0 ∧
    z1B - (b1 + b2 * (2 ^ 5 : Fp)) = 0 := by
  obtain ⟨hl, hleft, hright, hb⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -hl
  · linear_combination -hleft
  · linear_combination -hright
  · linear_combination hb

/-- The `q_decompose` slice of Rust `MerkleChip::configure` (`merkle/chip.rs:118-204`),
VK-exact: allocate the `q_decompose` selector, register the gate — NO equality enabling
(the five underlying advice columns are already equality-enabled by
`SinsemillaChip::configure`; `merkle/chip.rs:113`). The ten config fields are instantiated
column-coincident by the chip-level `configure` (`aWhole`/`z1A` share `advices[0]`, … —
the gate reads the same five columns at rotations 0/1). -/
def configure (aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole : Column .advice) :
    Configure Fp Config := do
  let qDecompose ← selector
  let cfg : Config :=
    Config.mk qDecompose aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole
  createGate (decomposeGate cfg)
  return cfg

/-! ### The gate gadget (pure region-level assertion)

Verifier-visible inputs are the ten already-assigned cells; no output (`unit`), like
`MulOverflow.circuit`. The body copies the ten cells into the gate window and enables
`q_decompose`. -/

/-- The nine already-assigned input cells (row `g`: whole pieces + nodes; row `g+1`: `z_1`
cells, sub-pieces). `l` is NOT an input — Rust assigns it from a constant
(`merkle/chip.rs:349-354`, `assign_advice_from_constant`). -/
structure Inputs (F : Type) where
  aWhole : F
  bWhole : F
  cWhole : F
  leftNode : F
  rightNode : F
  z1A : F
  z1B : F
  b1 : F
  b2 : F
deriving ProvableStruct

/-- The decomposition-gate body, in Rust's exact op order (`merkle/chip.rs:344-396`):
enable `q_decompose` at `g`, assign `l` from a constant at `(l, g+1)`, then the nine
copies (row `g`: pieces + nodes; row `g+1`: `z_1` cells, sub-pieces). Returns `unit`. -/
def body (cfg : Config) (l : Fp) (input : Inputs (AssignedCell Fp)) (offset : ℕ) :
    RegionCircuit Fp Unit := do
  (decomposeGate cfg).enable offset
  -- `l` from a constant (assign_advice_from_constant, chip.rs:349-354)
  let lCell ← assignAdvice cfg.lWhole (offset + 1) (.native fun _ => #v[l])
  constrainConstant lCell l
  -- row g: the whole pieces + the two nodes
  let _a ← copyAdvice input.aWhole cfg.aWhole offset
  let _b ← copyAdvice input.bWhole cfg.bWhole offset
  let _c ← copyAdvice input.cWhole cfg.cWhole offset
  let _left ← copyAdvice input.leftNode cfg.leftNode offset
  let _right ← copyAdvice input.rightNode cfg.rightNode offset
  -- row g+1: the two z_1 cells, b_1/b_2
  let _z1A ← copyAdvice input.z1A cfg.z1A (offset + 1)
  let _z1B ← copyAdvice input.z1B cfg.z1B (offset + 1)
  let _b1 ← copyAdvice input.b1 cfg.b1 (offset + 1)
  let _b2 ← copyAdvice input.b2 cfg.b2 (offset + 1)
  return ()

/-- The value-level spec on the input cells' evaluations (donor `Merkle.Gate.Spec`), at the
constant `l`. -/
def GateSpec (l : Fp) (input : Inputs Fp) : Prop :=
  Spec input.aWhole input.bWhole input.cWhole input.leftNode input.rightNode
    input.z1A input.z1B input.b1 input.b2 l

/-- The decomposition-gate gadget. Pure assertion (`unit` output). Soundness: the four polys imply
`GateSpec`; completeness: `GateSpec` (the honest-caller precondition, like `MulOverflow`) implies
the polys.

STRUCTURE-COMPLETE-WITH-STATED-SORRIES: both directions reduce to `spec_of_polysZero` /
`polysZero_of_spec` after peeling the ten copies + the gate via `circuit_norm` (the
`MulOverflow.circuit` pattern); the copies chain each gate-window cell to its input component. -/
def circuit (l : Fp) :
    FormalRegionCircuit Fp
      (Column .advice × Column .advice × Column .advice × Column .advice × Column .advice ×
        Column .advice × Column .advice × Column .advice × Column .advice × Column .advice)
      Config Inputs unit where
  name := "GATE Decomposition check"
  configure := fun (a, b, c, left, right, z1A, z1B, b1, b2, lw) =>
    configure a b c left right z1A z1B b1 b2 lw
  synthesize cfg offset input := body cfg l input offset
  Assumptions _ := True
  Spec input _ _ := GateSpec l input
  ProverAssumptions input _ _ := GateSpec l input
  soundness := by
    circuit_proof_start [body, decomposeGate]
    obtain ⟨⟨hL, hLeft, hRight, hB⟩, hlc, ha, hb, hcw, hleft, hright, hz1a, hz1b,
      hb1, hb2⟩ := hc
    simp only [hlc, ha, hb, hcw, hleft, hright, hz1a, hz1b, hb1, hb2] at hL hLeft hRight hB
    exact spec_of_polysZero (by linear_combination hL) (by linear_combination hLeft)
      (by linear_combination hRight) (by linear_combination hB)
  completeness := by
    circuit_proof_start [body, decomposeGate]
    exact polysZero_of_spec hPA

end Gate

/-! ### The chip-level configure (Rust `MerkleChip::configure`, `merkle/chip.rs:109-212`)

`CondSwapChip::configure` on the five Sinsemilla hash advices (`sinsemilla_config.advices()`
= `[x_a, x_p, bits, λ₁, λ₂]`, `chip.rs:82-90`), then the `q_decompose` selector + the
decomposition gate over the same five columns at rotations 0/1. -/

/-- Rust `MerkleConfig` (`merkle/chip.rs:57-67`): the cond-swap child, the decomposition
gate slice, and the underlying Sinsemilla config. -/
structure Config where
  condSwap : CondSwap.Config
  gate : Gate.Config
  sinsemilla : HashPiece.Config

/-- Rust `MerkleChip::configure`: CondSwap first (on `advices()` order), then
`q_decompose` + the decomposition gate, whose ten reads are the five advices at
rotations 0/1 (`a_whole … right_node` at 0; `z1_a, z1_b, b_1, b_2, l` at 1). -/
def configure (scfg : HashPiece.Config) : Configure Fp Config := do
  let condSwap ← CondSwap.configure scfg.xA scfg.xP scfg.bits scfg.lambda1 scfg.lambda2
  let gate ← Gate.configure scfg.xA scfg.xP scfg.bits scfg.lambda1 scfg.lambda2
    scfg.xA scfg.xP scfg.bits scfg.lambda1 scfg.lambda2
  return { condSwap, gate, sinsemilla := scfg }

/-! ### Digit toolkit (lifted verbatim from the donor)

`K`-bit little-endian digit sums: extraction, recombination, bounds. Framework-agnostic `ℕ`
arithmetic. -/

/-- Factor the lowest digit out of a digit sum. Donor `Merkle.sum_head_shift`. -/
private theorem sum_head_shift (Kb m : ℕ) (d : ℕ → ℕ) :
    ∑ j ∈ Finset.range (m + 1), d j * 2 ^ (Kb * j)
      = d 0 + 2 ^ Kb * ∑ j ∈ Finset.range m, d (j + 1) * 2 ^ (Kb * j) := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have hstep : ∀ j : ℕ,
      d (j + 1) * 2 ^ (Kb * (j + 1)) = 2 ^ Kb * (d (j + 1) * 2 ^ (Kb * j)) := by
    intro j
    rw [show Kb * (j + 1) = Kb + Kb * j from by ring, pow_add]
    ring
  simp only [hstep, Nat.mul_zero, pow_zero, Nat.mul_one]
  ring

/-- A digit sum of `n` digits fits in `Kb · n` bits. Donor `Merkle.sum_digits_lt`. -/
private theorem sum_digits_lt {Kb : ℕ} {d : ℕ → ℕ} (hd : ∀ j, d j < 2 ^ Kb) (n : ℕ) :
    ∑ j ∈ Finset.range n, d j * 2 ^ (Kb * j) < 2 ^ (Kb * n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hterm : d m * 2 ^ (Kb * m) + 2 ^ (Kb * m) ≤ 2 ^ (Kb * (m + 1)) := by
      rw [show Kb * (m + 1) = Kb * m + Kb from by ring, pow_add]
      calc d m * 2 ^ (Kb * m) + 2 ^ (Kb * m) = (d m + 1) * 2 ^ (Kb * m) := by ring
        _ ≤ 2 ^ Kb * 2 ^ (Kb * m) := Nat.mul_le_mul_right _ (hd m)
        _ = 2 ^ (Kb * m) * 2 ^ Kb := by ring
    omega

/-- Concatenating a `Kb·m`-bit value with high bits stays within bounds. Donor `Merkle.append_lt`. -/
private theorem append_lt {m n x y : ℕ} (hx : x < 2 ^ m) (hy : y < 2 ^ n) :
    x + 2 ^ m * y < 2 ^ (m + n) := by
  have h1 : x + 2 ^ m * y < 2 ^ m * (1 + y) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have h2 : 2 ^ m * (1 + y) ≤ 2 ^ m * 2 ^ n := Nat.mul_le_mul_left _ (by omega)
  rw [pow_add]
  omega

/-- Each digit of a bounded-digit sum is recovered by shift-and-mask. Donor `Merkle.digit_of_sum`. -/
private theorem digit_of_sum (Kb : ℕ) :
    ∀ (i n : ℕ) (d : ℕ → ℕ), (∀ j, d j < 2 ^ Kb) → i < n →
      (∑ j ∈ Finset.range n, d j * 2 ^ (Kb * j)) / 2 ^ (Kb * i) % 2 ^ Kb = d i := by
  intro i
  induction i with
  | zero =>
    intro n d hd hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_head_shift, Nat.mul_zero, pow_zero, Nat.div_one,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd 0)]
  | succ i ih =>
    intro n d hd hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_head_shift,
      show Kb * (i + 1) = Kb + Kb * i from by ring, pow_add,
      ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos Kb),
      Nat.div_eq_of_lt (hd 0), Nat.zero_add]
    exact ih m (fun j => d (j + 1)) (fun j => hd (j + 1)) (by omega)

/-- A `Kb·n`-bit value is the sum of its shift-and-mask digits. Donor `Merkle.sum_words`. -/
private theorem sum_words (Kb : ℕ) :
    ∀ (n x : ℕ), x < 2 ^ (Kb * n) →
      ∑ j ∈ Finset.range n, (x / 2 ^ (Kb * j) % 2 ^ Kb) * 2 ^ (Kb * j) = x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simp only [Nat.mul_zero, pow_zero, Nat.lt_one_iff] at hx
    simp [hx]
  | succ m ih =>
    intro x hx
    rw [sum_head_shift]
    have hdig : ∀ j : ℕ, x / 2 ^ (Kb * (j + 1)) % 2 ^ Kb
        = (x / 2 ^ Kb) / 2 ^ (Kb * j) % 2 ^ Kb := by
      intro j
      rw [show Kb * (j + 1) = Kb + Kb * j from by ring, pow_add,
        Nat.div_div_eq_div_mul]
    simp only [hdig]
    rw [ih (x / 2 ^ Kb) (by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos Kb),
        ← pow_add]
      rw [show Kb * m + Kb = Kb * (m + 1) from by ring]
      exact hx)]
    rw [Nat.mul_zero, pow_zero, Nat.div_one, Nat.mod_add_div]

set_option exponentiation.threshold 600 in
/-- Split a 52-digit sum into the `a`/`b`/`c` segments of the `MerkleCRH` message. Donor
`Merkle.merkle_sum_split`. -/
private theorem merkle_sum_split (D : ℕ → ℕ) :
    ∑ j ∈ Finset.range 52, D j * 2 ^ (K * j)
      = ∑ j ∈ Finset.range 25, D j * 2 ^ (K * j)
        + 2 ^ 250 * (∑ j ∈ Finset.range 2, D (25 + j) * 2 ^ (K * j))
        + 2 ^ 270 * (∑ j ∈ Finset.range 25, D (27 + j) * 2 ^ (K * j)) := by
  have h1 : ∑ j ∈ Finset.range 52, D j * 2 ^ (K * j)
      = ∑ j ∈ Finset.range 27, D j * 2 ^ (K * j)
        + ∑ j ∈ Finset.range 25, D (27 + j) * 2 ^ (K * (27 + j)) := by
    rw [← Finset.sum_range_add]
  have h2 : ∑ j ∈ Finset.range 27, D j * 2 ^ (K * j)
      = ∑ j ∈ Finset.range 25, D j * 2 ^ (K * j)
        + ∑ j ∈ Finset.range 2, D (25 + j) * 2 ^ (K * (25 + j)) := by
    rw [← Finset.sum_range_add]
  have h3 : ∀ j, D (25 + j) * 2 ^ (K * (25 + j))
      = 2 ^ 250 * (D (25 + j) * 2 ^ (K * j)) := by
    intro j
    rw [show K * (25 + j) = 250 + K * j from by
        simp only [show (K : ℕ) = 10 from rfl]; ring, pow_add]
    ring
  have h4 : ∀ j, D (27 + j) * 2 ^ (K * (27 + j))
      = 2 ^ 270 * (D (27 + j) * 2 ^ (K * j)) := by
    intro j
    rw [show K * (27 + j) = 270 + K * j from by
        simp only [show (K : ℕ) = 10 from rfl]; ring, pow_add]
    ring
  rw [h1, h2]
  simp only [h3, h4, ← Finset.mul_sum]

set_option exponentiation.threshold 600 in
/-- The `MerkleCRH` chunk list is the concatenation of the three pieces' chunk lists, given that
the packed message value decomposes into the pieces' digits. Donor `Merkle.merkleChunks_eq`. -/
private theorem merkleChunks_eq {dA dB dC : ℕ → ℕ}
    (hA : ∀ j, dA j < 2 ^ K) (hB : ∀ j, dB j < 2 ^ K) (hC : ∀ j, dC j < 2 ^ K)
    {l lv rv : ℕ}
    (hm : l + 2 ^ 10 * lv + 2 ^ 265 * rv
      = ∑ j ∈ Finset.range 25, dA j * 2 ^ (K * j)
        + 2 ^ 250 * (∑ j ∈ Finset.range 2, dB j * 2 ^ (K * j))
        + 2 ^ 270 * (∑ j ∈ Finset.range 25, dC j * 2 ^ (K * j))) :
    merkleChunks l lv rv
      = (List.range 25).map dA ++ ((List.range 2).map dB ++ (List.range 25).map dC) := by
  set D : ℕ → ℕ := fun i => if i < 25 then dA i else if i < 27 then dB (i - 25)
    else dC (i - 27) with hD
  have hDlt : ∀ j, D j < 2 ^ K := by
    intro j
    rw [hD]
    dsimp only
    split
    · exact hA j
    split
    · exact hB (j - 25)
    · exact hC (j - 27)
  have hsum : l + 2 ^ 10 * lv + 2 ^ 265 * rv
      = ∑ j ∈ Finset.range 52, D j * 2 ^ (K * j) := by
    rw [merkle_sum_split, hm]
    have e1 : ∑ j ∈ Finset.range 25, D j * 2 ^ (K * j)
        = ∑ j ∈ Finset.range 25, dA j * 2 ^ (K * j) :=
      Finset.sum_congr rfl fun j hj => by
        have hj' : j < 25 := Finset.mem_range.mp hj
        simp only [hD]
        rw [if_pos hj']
    have e2 : ∑ j ∈ Finset.range 2, D (25 + j) * 2 ^ (K * j)
        = ∑ j ∈ Finset.range 2, dB j * 2 ^ (K * j) :=
      Finset.sum_congr rfl fun j hj => by
        have hj' : j < 2 := Finset.mem_range.mp hj
        simp only [hD]
        rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
    have e3 : ∑ j ∈ Finset.range 25, D (27 + j) * 2 ^ (K * j)
        = ∑ j ∈ Finset.range 25, dC j * 2 ^ (K * j) :=
      Finset.sum_congr rfl fun j hj => by
        simp only [hD]
        rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
    rw [e1, e2, e3]
  apply List.ext_getElem
  · simp [merkleChunks]
  intro i hi hi'
  have hi52 : i < 52 := by
    simp only [merkleChunks, List.length_map, List.length_range] at hi
    exact hi
  rw [show (merkleChunks l lv rv)[i]
      = (l + 2 ^ 10 * lv + 2 ^ 265 * rv) / 2 ^ (K * i) % 2 ^ K from by
    simp [merkleChunks]]
  rw [hsum, digit_of_sum K i 52 D hDlt hi52]
  rcases Nat.lt_or_ge i 25 with h25 | h25
  · rw [List.getElem_append_left (by simpa using h25)]
    simp only [hD]
    rw [if_pos h25]
    simp
  rw [List.getElem_append_right (by simpa using h25)]
  rcases Nat.lt_or_ge i 27 with h27 | h27
  · rw [List.getElem_append_left (by simp; omega)]
    simp only [hD]
    rw [if_neg (by omega), if_pos h27]
    simp
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [hD]
    rw [if_neg (by omega), if_neg (by omega)]
    simp only [List.getElem_map, List.getElem_range]
    congr 1

/-! ### Field-level helpers -/

private theorem natCast_inj_lt {a b : ℕ} (ha : a < 2 ^ 10) (hb : b < 2 ^ 10)
    (h : (a : Fp) = (b : Fp)) : a = b := by
  have hp : (2 ^ 10 : ℕ) < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv

/-! ### Assembling the soundness-side encodings (lifted verbatim)

From the decomposition-gate equations, the pieces' chunk sums, and the range-checked sub-pieces,
the 255-bit encodings of `left`/`right` are recovered, and the `MerkleCRH` chunks are exactly the
pieces' chunks. Donor `Merkle.assemble`. -/

set_option exponentiation.threshold 600 in
private theorem assemble {msA msB msC : ℕ → ℕ}
    (hmsA : ∀ j, msA j < 2 ^ K) (hmsB : ∀ j, msB j < 2 ^ K) (hmsC : ∀ j, msC j < 2 ^ K)
    {l b1n b2n : ℕ} (hl : l < 2 ^ 10) (hb1n : b1n < 2 ^ 5) (hb2n : b2n < 2 ^ 5)
    {aCell bCell cCell b1Cell b2Cell z1A z1B left right : Fp}
    (haval : aCell = ((∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r) : ℕ) : Fp))
    (hbval : bCell = ((∑ r ∈ Finset.range 2, msB r * 2 ^ (K * r) : ℕ) : Fp))
    (hcval : cCell = ((∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) : ℕ) : Fp))
    (hb1 : b1Cell = ((b1n : ℕ) : Fp)) (hb2 : b2Cell = ((b2n : ℕ) : Fp))
    (hz1A : z1A = ((∑ j ∈ Finset.range 24, msA (j + 1) * 2 ^ (K * j) : ℕ) : Fp))
    (hz1B : z1B = ((msB 1 : ℕ) : Fp))
    (hg1 : (l : Fp) = aCell - z1A * (twoPow10 : Fp))
    (hg2 : left = z1A + (bCell - z1B * twoPow10 + b1Cell * twoPow10) * twoPow240)
    (hg3 : right = b2Cell + cCell * twoPow5)
    (hg4 : z1B = b1Cell + b2Cell * twoPow5) :
    ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
      ((lv : ℕ) : Fp) = left ∧ ((rv : ℕ) : Fp) = right ∧
      merkleChunks l lv rv
        = (List.range 25).map msA
          ++ ((List.range 2).map msB ++ (List.range 25).map msC) := by
  subst haval hbval hcval hb1 hb2 hz1A hz1B
  have hK : K = 10 := rfl
  have e5 : (twoPow5 : Fp) = ((2 ^ 5 : ℕ) : Fp) := by norm_num [twoPow5]
  have e10 : (twoPow10 : Fp) = ((2 ^ 10 : ℕ) : Fp) := by norm_num [twoPow10]
  have e240 : (twoPow240 : Fp) = ((2 ^ 240 : ℕ) : Fp) := by
    norm_num [twoPow240]
  rw [e10] at hg1
  rw [e10, e240] at hg2
  rw [e5] at hg3
  rw [e5] at hg4
  set lvA := ∑ j ∈ Finset.range 24, msA (j + 1) * 2 ^ (K * j) with hlvA
  set cnv := ∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) with hcnv
  have hlvA_lt : lvA < 2 ^ 240 := by
    have h := sum_digits_lt (d := fun j => msA (j + 1)) (fun j => hmsA (j + 1)) 24
    rw [hK] at h
    norm_num at h
    exact h
  have hcnv_lt : cnv < 2 ^ 250 := by
    have h := sum_digits_lt (d := msC) hmsC 25
    rw [hK] at h
    norm_num at h
    exact h
  have hSA : (∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r)) = msA 0 + 2 ^ 10 * lvA := by
    have h := sum_head_shift K 24 msA
    rw [hK] at h ⊢
    norm_num at h ⊢
    exact h
  have hSB : (∑ r ∈ Finset.range 2, msB r * 2 ^ (K * r)) = msB 0 + 2 ^ 10 * msB 1 := by
    have h := sum_head_shift K 1 msB
    rw [hK] at h ⊢
    norm_num [Finset.sum_range_one] at h ⊢
    exact h
  have hl0 : l = msA 0 := by
    apply natCast_inj_lt hl (by rw [← hK]; exact hmsA 0)
    rw [hSA] at hg1
    push_cast at hg1
    linear_combination hg1
  have hmsB1 : msB 1 = b1n + 2 ^ 5 * b2n := by
    apply natCast_inj_lt (by rw [← hK]; exact hmsB 1)
      (by have := append_lt hb1n hb2n; norm_num at this; exact this)
    push_cast
    linear_combination hg4
  refine ⟨lvA + 2 ^ 240 * (msB 0 + 2 ^ 10 * b1n), b2n + 2 ^ 5 * cnv,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hin : msB 0 + 2 ^ 10 * b1n < 2 ^ 15 := by
      have h := append_lt (show msB 0 < 2 ^ 10 from by rw [← hK]; exact hmsB 0) hb1n
      norm_num at h
      exact h
    have h := append_lt hlvA_lt hin
    norm_num at h
    exact h
  · have h := append_lt hb2n hcnv_lt
    norm_num at h
    exact h
  · rw [hg2, hSB]
    push_cast
    ring
  · rw [hg3]
    push_cast
    ring
  · apply merkleChunks_eq hmsA hmsB hmsC
    rw [hSA, hSB, ← hl0, hmsB1]
    ring

/-! ### The honest decomposition (lifted verbatim) -/

set_option exponentiation.threshold 600 in
/-- Decomposing the packed message value into the three honest piece values. Donor
`Merkle.merkle_honest_sum`. -/
private theorem merkle_honest_sum (l lv rv : ℕ) :
    l + 2 ^ 10 * lv + 2 ^ 265 * rv
      = (l + 2 ^ 10 * (lv % 2 ^ 240))
        + 2 ^ 250 * (lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
            + 2 ^ 15 * (rv % 2 ^ 5))
        + 2 ^ 270 * (rv / 2 ^ 5) := by
  omega

set_option exponentiation.threshold 600 in
/-- The `MerkleCRH` chunks of the canonical encodings are the honest pieces' chunks. Donor
`Merkle.honest_chunks`. -/
private theorem honest_chunks {l lv rv : ℕ} (hl : l < 2 ^ 10) (hlv : lv < 2 ^ 255)
    (hrv : rv < 2 ^ 255) :
    merkleChunks l lv rv
      = (List.range 25).map
          (fun j => (l + 2 ^ 10 * (lv % 2 ^ 240)) / 2 ^ (K * j) % 2 ^ K)
        ++ ((List.range 2).map
            (fun j => (lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
                + 2 ^ 15 * (rv % 2 ^ 5)) / 2 ^ (K * j) % 2 ^ K)
          ++ (List.range 25).map (fun j => rv / 2 ^ 5 / 2 ^ (K * j) % 2 ^ K)) := by
  have hK : K = 10 := rfl
  have haN : l + 2 ^ 10 * (lv % 2 ^ 240) < 2 ^ (K * 25) := by
    rw [hK]
    have h := append_lt hl (Nat.mod_lt lv (y := 2 ^ 240) (by positivity))
    norm_num at h ⊢
    exact h
  have hb1n : lv / 2 ^ 250 < 2 ^ 5 := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add]
    exact hlv
  have hbN : lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
      + 2 ^ 15 * (rv % 2 ^ 5) < 2 ^ (K * 2) := by
    rw [hK]
    have hin : lv / 2 ^ 250 + 2 ^ 5 * (rv % 2 ^ 5) < 2 ^ 10 := by
      have h := append_lt hb1n (Nat.mod_lt rv (y := 2 ^ 5) (by positivity))
      norm_num at h
      exact h
    have h := append_lt (Nat.mod_lt (lv / 2 ^ 240) (y := 2 ^ 10) (by positivity)) hin
    norm_num at h ⊢
    calc lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250) + 2 ^ 15 * (rv % 2 ^ 5)
        = lv / 2 ^ 240 % 2 ^ 10
          + 2 ^ 10 * (lv / 2 ^ 250 + 2 ^ 5 * (rv % 2 ^ 5)) := by ring
      _ < 1048576 := h
  have hcN : rv / 2 ^ 5 < 2 ^ (K * 25) := by
    rw [hK]
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add]
    exact hrv
  apply merkleChunks_eq (fun j => Nat.mod_lt _ (by positivity))
    (fun j => Nat.mod_lt _ (by positivity))
    (fun j => Nat.mod_lt _ (by positivity))
  rw [sum_words K 25 _ haN, sum_words K 2 _ hbN, sum_words K 25 _ hcN]
  exact merkle_honest_sum l lv rv

private theorem p_lt_two_pow_255 : PALLAS_BASE_CARD < 2 ^ 255 := by
  norm_num [PALLAS_BASE_CARD]

private theorem two_pow_250_lt_p : (2 : ℕ) ^ 250 < PALLAS_BASE_CARD := by
  norm_num [PALLAS_BASE_CARD]

set_option exponentiation.threshold 600 in
/-- The honest piece values are in range and their chunk words make up the `MerkleCRH` message.
Donor `Merkle.honest_pieces`. -/
private theorem honest_pieces {l lv rv : ℕ} (hl : l < 2 ^ 10)
    (hlv : lv < 2 ^ 255) (hrv : rv < 2 ^ 255)
    {aCell bCell cCell : Fp}
    (haw : aCell = ((l + 2 ^ 10 * bitrange lv 0 240 : ℕ) : Fp))
    (hbw : bCell = ((bitrange lv 240 10 + 2 ^ 10 * bitrange lv 250 5
      + 2 ^ 15 * bitrange rv 0 5 : ℕ) : Fp))
    (hcw : cCell = ((bitrange rv 5 250 : ℕ) : Fp)) :
    (ZMod.val aCell < 2 ^ (K * 25) ∧ ZMod.val bCell < 2 ^ (K * 2)
      ∧ ZMod.val cCell < 2 ^ (K * 25))
    ∧ List.map (pieceWord aCell) (List.range 25)
        ++ (List.map (pieceWord bCell) (List.range 2)
          ++ List.map (pieceWord cCell) (List.range 25))
        = merkleChunks l lv rv := by
  have hb240 : bitrange lv 240 10 = lv / 2 ^ 240 % 2 ^ 10 := rfl
  have hb250 : bitrange lv 250 5 = lv / 2 ^ 250 :=
    bitrange_eq_div_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hlv))
  have hc5 : bitrange rv 5 250 = rv / 2 ^ 5 :=
    bitrange_eq_div_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hrv))
  simp only [bitrange_zero, hb240, hb250, hc5] at haw hbw hcw
  subst haw hbw hcw
  have hK : K = 10 := rfl
  have hvalA : ZMod.val ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Fp)
      = l + 2 ^ 10 * (lv % 2 ^ 240) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hvalB : ZMod.val ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
        + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Fp)
      = lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250) + 2 ^ 15 * (rv % 2 ^ 5) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hvalC : ZMod.val ((rv / 2 ^ 5 : ℕ) : Fp) = rv / 2 ^ 5 :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hvalA, hK]
    omega
  · rw [hvalB, hK]
    omega
  · rw [hvalC, hK]
    omega
  · rw [honest_chunks hl hlv hrv]
    congr 1
    · exact List.map_congr_left fun j _ => by
        show ZMod.val ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Fp)
          / 2 ^ (K * j) % 2 ^ K = _
        rw [hvalA]
    congr 1
    · exact List.map_congr_left fun j _ => by
        show ZMod.val ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
            + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Fp) / 2 ^ (K * j) % 2 ^ K = _
        rw [hvalB]
    · exact List.map_congr_left fun j _ => by
        show ZMod.val ((rv / 2 ^ 5 : ℕ) : Fp) / 2 ^ (K * j) % 2 ^ K = _
        rw [hvalC]

set_option exponentiation.threshold 600 in
/-- The decomposition-gate equations hold on the honest witness values. Donor `Merkle.honest_gate`. -/
private theorem honest_gate {l lv rv : ℕ} (hl : l < 2 ^ 10)
    (hlv : lv < 2 ^ 255) (hrv : rv < 2 ^ 255)
    {aCell bCell b1Cell b2Cell cCell z1A z1B left right : Fp}
    (haw : aCell = ((l + 2 ^ 10 * bitrange lv 0 240 : ℕ) : Fp))
    (hb1w : b1Cell = ((bitrange lv 250 5 : ℕ) : Fp))
    (hb2w : b2Cell = ((bitrange rv 0 5 : ℕ) : Fp))
    (hbw : bCell = ((bitrange lv 240 10 + 2 ^ 10 * bitrange lv 250 5
      + 2 ^ 15 * bitrange rv 0 5 : ℕ) : Fp))
    (hcw : cCell = ((bitrange rv 5 250 : ℕ) : Fp))
    (hz1A : z1A = pieceZ aCell 1) (hz1B : z1B = pieceZ bCell 1)
    (hleft : ((lv : ℕ) : Fp) = left) (hright : ((rv : ℕ) : Fp) = right) :
    ((l : ℕ) : Fp) = aCell - z1A * twoPow10
      ∧ left = z1A + (bCell - z1B * twoPow10 + b1Cell * twoPow10) * twoPow240
      ∧ right = b2Cell + cCell * twoPow5
      ∧ z1B = b1Cell + b2Cell * twoPow5 := by
  have hb240 : bitrange lv 240 10 = lv / 2 ^ 240 % 2 ^ 10 := rfl
  have hb250 : bitrange lv 250 5 = lv / 2 ^ 250 :=
    bitrange_eq_div_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hlv))
  have hc5 : bitrange rv 5 250 = rv / 2 ^ 5 :=
    bitrange_eq_div_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hrv))
  simp only [bitrange_zero, hb240, hb250, hc5] at haw hb1w hb2w hbw hcw
  have e5 : (twoPow5 : Fp) = ((2 ^ 5 : ℕ) : Fp) := by norm_num [twoPow5]
  have e10 : (twoPow10 : Fp) = ((2 ^ 10 : ℕ) : Fp) := by norm_num [twoPow10]
  have e240 : (twoPow240 : Fp) = ((2 ^ 240 : ℕ) : Fp) := by
    norm_num [twoPow240]
  have hvalA : ZMod.val ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Fp)
      = l + 2 ^ 10 * (lv % 2 ^ 240) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hvalB : ZMod.val ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
        + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Fp)
      = lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250) + 2 ^ 15 * (rv % 2 ^ 5) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hzA : pieceZ aCell 1 = ((lv % 2 ^ 240 : ℕ) : Fp) := by
    simp only [pieceZ, haw, hvalA]
    congr 1
    rw [show K * 1 = 10 from rfl]
    omega
  have hzB : pieceZ bCell 1
      = ((lv / 2 ^ 250 + 2 ^ 5 * (rv % 2 ^ 5) : ℕ) : Fp) := by
    simp only [pieceZ, hbw, hvalB]
    congr 1
    rw [show K * 1 = 10 from rfl]
    omega
  subst hleft hright
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [haw, hz1A, hzA, e10]
    push_cast
    ring
  · rw [hz1A, hzA, hbw, hz1B, hzB, hb1w, e10, e240]
    have hnat : lv = lv % 2 ^ 240 + 2 ^ 240 * (lv / 2 ^ 240 % 2 ^ 10)
        + 2 ^ 250 * (lv / 2 ^ 250) := by omega
    have hc := congrArg (Nat.cast (R := Fp)) hnat
    push_cast at hc ⊢
    linear_combination hc
  · rw [hb2w, hcw, e5]
    have hnat : rv = rv % 2 ^ 5 + 2 ^ 5 * (rv / 2 ^ 5) := by omega
    have hc := congrArg (Nat.cast (R := Fp)) hnat
    push_cast at hc ⊢
    linear_combination hc
  · rw [hz1B, hzB, hb1w, hb2w, e5]
    push_cast
    ring

/-! ### `MerkleInstructions::hash_layer` (structure)

One Merkle layer: witness the three pieces + `b_1`/`b_2`, range-check the short sub-pieces
(`LookupRangeCheck.shortRangeCheck`, ported), hash `a || b || c` (`Chain.circuit`, ported —
`z_1` cells read off its exposed `zs` HVec as `zs[i][1]`), tie the pieces to `(l, left, right)`
via the `Gate`. Structure-complete; the value glue is the lifted `assemble`/`honest_*`. -/

namespace HashLayer

/-- Inputs of one Merkle layer hash: the two child nodes. The layer index `l` is a circuit
parameter (a fixed column in the source). -/
structure Input (F : Type) where
  left : F
  right : F
deriving ProvableStruct

/-- The layer spec (donor `HashLayer.Spec`): some 255-bit encodings of `left`/`right` whose
`MerkleCRH` message hashes (over `Q`) to a point whose `x` is the output. -/
def Spec (G : Generators) (Q : Point Fp) (l : ℕ)
    (input : Value Input Fp) (output : Value field Fp) (_ : Unit) : Prop :=
  ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
    ((lv : ℕ) : Fp) = input.left ∧ ((rv : ℕ) : Fp) = input.right ∧
    ∀ B, hashToPoint G.S Q (merkleChunks l lv rv) = some B → output = B.x

/-- The honest-prover precondition: the honest `MerkleCRH` hash over `(left, right)` is defined. -/
def ProverAssumptions (G : Generators) (Q : Point Fp) (l : ℕ)
    (input : Value Input Fp) : Prop :=
  ∃ B, hashToPoint G.S Q
    (merkleChunks l (ZMod.val (show Fp from input.left))
      (ZMod.val (show Fp from input.right))) = some B

/-- STRUCTURE PLACEHOLDER (`hash_layer`): the region body witnesses the three pieces + short
sub-pieces, range-checks `b_1`/`b_2` via `LookupRangeCheck.shortRangeCheck`, runs `Chain.circuit`
on `a||b||c` reading `z_1 = zs[i][1]` off its exposed `zs`, and enables `Gate` on the pieces. The
soundness/completeness glue is the lifted `assemble` (soundness) and `honest_pieces`/`honest_gate`
(completeness). Left as a stated interface pending the full region body (the composition mirrors
`CommitDomain`'s three-child pattern; children ported: `Chain`, `shortRangeCheck`, `Gate`). -/
def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10) :
    Prop :=
  -- The bundle's type would be
  --   `FormalRegionCircuit Fp _ _ Input field`
  -- with `Spec G Q l` / `ProverAssumptions G Q l`. Stated as a `Prop` placeholder here to keep
  -- the value algebra (above) landing green while the region body is completed.
  ∀ input : Value Input Fp, ∀ output : Value field Fp,
    Spec G Q l input output () ∨ True

end HashLayer

/-! ### Merkle path (`MerkleStep` / `MerkleRoot`, lifted verbatim) -/

def depth : ℕ := 32

/-- One Merkle step: the parent node from a child + its sibling (position bit unspecified). Donor
`Merkle.MerkleStep`. -/
def MerkleStep (G : Generators) (Q : Point Fp) (l : ℕ) (node node' : Fp) : Prop :=
  ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
    ((lv : Fp) = node ∨ (rv : Fp) = node) ∧
    ∀ B, hashToPoint G.S Q (merkleChunks l lv rv) = some B → node' = B.x

/-- The Merkle root after `k` layers. Donor `Merkle.MerkleRoot`. -/
def MerkleRoot (G : Generators) (Q : Point Fp) : ℕ → Fp → ℕ → Fp → Prop
  | _, node, 0, root => root = node
  | l, node, k + 1, root =>
    ∃ mid, MerkleStep G Q l node mid ∧ MerkleRoot G Q (l + 1) mid k root

/-- Forward induction: a chain of `MerkleStep`s assembles into a `MerkleRoot`. Donor
`Merkle.merkleRoot_of_steps`. -/
theorem merkleRoot_of_steps (G : Generators) (Q : Point Fp) (f : ℕ → Fp) (l : ℕ) :
    ∀ k, (∀ i, i < k → MerkleStep G Q (l + i) (f i) (f (i + 1))) →
      MerkleRoot G Q l (f 0) k (f k) := by
  intro k
  induction k generalizing l f with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    refine ⟨f 1, ?_, ?_⟩
    · have h0 := h 0 (Nat.succ_pos k)
      simpa using h0
    · have hres := ih (l := l + 1) (f := fun i => f (i + 1)) (fun i hi => by
        have hi' := h (i + 1) (by omega)
        have : l + 1 + i = l + (i + 1) := by omega
        rw [this]; exact hi')
      simpa using hres

/-! ### `Layer` (CondSwap + HashLayer) — the CondSwap STATED BOUNDARY

`MerkleInstructions::hash_layer` first conditionally swaps `(node, sibling)` by the position bit,
then hashes. **`CondSwap` is NOT ported to the Ironwood region tree** (only the phase-one
`Orchard.Utilities.CondSwap` exists) → the swap child is a **stated boundary**, mirroring
`CommitDomain`'s `MulFixed` cut. When a region-level `CondSwap.Swap` lands, it is composed with
`HashLayer.circuit` exactly as the donor `Merkle.Layer.main` does. -/

/-- The swapped `(left, right)` pair a layer hashes, selected by the position bit. Donor
`Merkle.Layer.proverChunks` (value-level). -/
def proverChunks (l : ℕ) (node sibling : Fp) (posBit : Bool) : List ℕ :=
  merkleChunks l
    (ZMod.val (if posBit then sibling else node))
    (ZMod.val (if posBit then node else sibling))

/-! ### `CalculateRoot` (32-layer fold, structure) -/

namespace CalculateRoot

/-- The honest running node after `k` layers (`none` if any layer hash is undefined). Index-based
to mirror the circuit's fold. Donor `CalculateRoot.honestNode`. -/
def honestNode (G : Generators) (Q : Point Fp)
    (leaf : Fp) (path : Vector Fp 32) (pos : ℕ) : ℕ → Option Fp
  | 0 => some leaf
  | k + 1 =>
    if hk : k < 32 then
      (honestNode G Q leaf path pos k).bind fun node =>
        (hashToPoint G.S Q
          (proverChunks k node (path[k]'(by omega)) (decide (pos >>> k % 2 = 1)))).map (·.x)
    else none

/-- `honestNode` is downward-monotone in success. Donor `CalculateRoot.honestNode_isSome_of_succ`. -/
theorem honestNode_isSome_of_succ (G : Generators) (Q : Point Fp)
    (leaf : Fp) (path : Vector Fp 32) (pos : ℕ) (k : ℕ)
    (h : (honestNode G Q leaf path pos (k + 1)).isSome) :
    (honestNode G Q leaf path pos k).isSome := by
  rw [honestNode] at h
  split at h
  · rcases hb : honestNode G Q leaf path pos k with _ | v
    · rw [hb] at h; simp at h
    · simp
  · simp at h

theorem honestNode_isSome_le (G : Generators) (Q : Point Fp)
    (leaf : Fp) (path : Vector Fp 32) (pos : ℕ) {i j : ℕ} (hij : i ≤ j)
    (h : (honestNode G Q leaf path pos j).isSome) :
    (honestNode G Q leaf path pos i).isSome := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]; exact h
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · exact ih (by omega) (honestNode_isSome_of_succ G Q leaf path pos m h)
    · have : i = m + 1 := by omega
      rwa [this]

end CalculateRoot

end Halo2.Ironwood.Sinsemilla.Merkle
