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
import Clean.Ironwood.Sinsemilla.HashToPoint

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
  name := "Check piece decomposition"
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

/-- The honest piece/sub-piece witness programs, computed off the node cells (Rust
`bitrange_subset` values, `Value`-view). `lv`/`rv` are the canonical node values. -/
def waWit (l : ℕ) (left : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((l + 2 ^ 10 * bitrange (Sinsemilla.HashPiece.readCell env left).val 0 240 : ℕ) : Fp)]

def wb1Wit (left : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[((bitrange (Sinsemilla.HashPiece.readCell env left).val 250 5 : ℕ) : Fp)]

def wb2Wit (right : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[((bitrange (Sinsemilla.HashPiece.readCell env right).val 0 5 : ℕ) : Fp)]

def wbWit (left right : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((bitrange (Sinsemilla.HashPiece.readCell env left).val 240 10
        + 2 ^ 10 * bitrange (Sinsemilla.HashPiece.readCell env left).val 250 5
        + 2 ^ 15 * bitrange (Sinsemilla.HashPiece.readCell env right).val 0 5 : ℕ) : Fp)]

def wcWit (right : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[((bitrange (Sinsemilla.HashPiece.readCell env right).val 5 250 : ℕ) : Fp)]

/-- The MerkleCRH piece widths (25/2/25 words). -/
def merkleNs : List ℕ := [24, 1, 24]

/-- Rust `MerkleInstructions::hash_layer` (`merkle/chip.rs:229-436`), layouter-level, in the
Rust region sequence: witness `a`, short-range-check `b_1`/`b_2` (5 bits), witness `b`/`c`,
`hash_to_point` (the `hashMessage` region), the `"Check piece decomposition"` gate region.
Output: the hash point's `x` cell. -/
def synthesize (G : Generators) (cfg : Config)
    (lookupCfg : Halo2.Ironwood.LookupRangeCheck.Config 10) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ)
    (input : Var Input Fp) : Circuit Fp (Var field Fp) := do
  -- chip.rs:255-306 — witness a; range-check b1/b2; witness b, c
  let pa ← HashToPoint.witnessMessagePiece cfg.sinsemilla (waWit l input.left)
  let b1 ← Halo2.Ironwood.LookupRangeCheck.witnessShortCheck 10 5 lookupCfg
    (wb1Wit input.left)
  let b2 ← Halo2.Ironwood.LookupRangeCheck.witnessShortCheck 10 5 lookupCfg
    (wb2Wit input.right)
  let pb ← HashToPoint.witnessMessagePiece cfg.sinsemilla (wbWit input.left input.right)
  let pc ← HashToPoint.witnessMessagePiece cfg.sinsemilla (wcWit input.right)
  -- chip.rs:322-330 — the hash (the formal hash_to_point bundle)
  let out ← HashToPoint.hashMessage G merkleNs cfg.sinsemilla Q hQ (by decide)
    ⟨#v[pa, pb, pc]⟩
  -- chip.rs:337-397 — the decomposition-gate region
  let _ ← assignRegion "Check piece decomposition"
    ((Gate.circuit (l : Fp)).call cfg.gate 0
      { aWhole := pa, bWhole := pb, cWhole := pc,
        leftNode := input.left, rightNode := input.right,
        z1A := out.z1s[0], z1B := out.z1s[1], b1 := b1, b2 := b2 })
  pure out.point.x

end HashLayer

/-- Literal-eval bridge for the gate-input record (component-wise cell evals). -/
private theorem gateInputs_eval_literal (env : Placed Environment Fp)
    (a b c ln rn zA zB s1 s2 : AssignedCell Fp) :
    (eval env ({ aWhole := a, bWhole := b, cWhole := c, leftNode := ln, rightNode := rn,
                 z1A := zA, z1B := zB, b1 := s1, b2 := s2 } : Gate.Inputs (AssignedCell Fp))
      : Value Gate.Inputs Fp)
      = { aWhole := AssignedCell.eval env.place env.env a,
          bWhole := AssignedCell.eval env.place env.env b,
          cWhole := AssignedCell.eval env.place env.env c,
          leftNode := AssignedCell.eval env.place env.env ln,
          rightNode := AssignedCell.eval env.place env.env rn,
          z1A := AssignedCell.eval env.place env.env zA,
          z1B := AssignedCell.eval env.place env.env zB,
          b1 := AssignedCell.eval env.place env.env s1,
          b2 := AssignedCell.eval env.place env.env s2 } := by
  rw [ProvableStruct.eval_cells_eq_eval]
  with_unfolding_all rfl

/-- Literal-eval bridge for the gate-input record, prover view. -/
private theorem gateInputs_eval_literal_prover (env : Placed ProverEnvironment Fp)
    (a b c ln rn zA zB s1 s2 : AssignedCell Fp) :
    (eval env ({ aWhole := a, bWhole := b, cWhole := c, leftNode := ln, rightNode := rn,
                 z1A := zA, z1B := zB, b1 := s1, b2 := s2 } : Gate.Inputs (AssignedCell Fp))
      : Value Gate.Inputs Fp)
      = { aWhole := AssignedCell.eval env.place env.env.toEnvironment a,
          bWhole := AssignedCell.eval env.place env.env.toEnvironment b,
          cWhole := AssignedCell.eval env.place env.env.toEnvironment c,
          leftNode := AssignedCell.eval env.place env.env.toEnvironment ln,
          rightNode := AssignedCell.eval env.place env.env.toEnvironment rn,
          z1A := AssignedCell.eval env.place env.env.toEnvironment zA,
          z1B := AssignedCell.eval env.place env.env.toEnvironment zB,
          b1 := AssignedCell.eval env.place env.env.toEnvironment s1,
          b2 := AssignedCell.eval env.place env.env.toEnvironment s2 } := by
  rw [ProvableStruct.eval_cells_eq_eval_prover]
  with_unfolding_all rfl

-- contract bridges for the children
derive_contract_bridges shortC (K : ℕ) (numBits : ℕ) :=
  Halo2.Ironwood.LookupRangeCheck.shortRangeCheck K numBits

derive_contract_bridges gateC (lv : Fp) := Gate.circuit lv

-- contract bridges for the children (hand-written for the proof-typed binders)
private theorem hashC_spec_eq (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : HashLayer.merkleNs ≠ []) :
    (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ hns).Spec
      = fun input output wit => HashToPoint.Spec G HashLayer.merkleNs Q input output wit := rfl

private theorem hashC_assumptions_eq (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : HashLayer.merkleNs ≠ []) :
    (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ hns).Assumptions = fun _ => True := rfl

private theorem hashC_envAssumptions_eq (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : HashLayer.merkleNs ≠ [])
    (cfg : Sinsemilla.HashPiece.Config) (env : Placed Environment Fp) :
    (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ hns).EnvAssumptions cfg env
      = Sinsemilla.GeneratorTableLoaded G cfg.generatorTable env.env := rfl

private theorem hashC_proverAssumptions_eq (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : HashLayer.merkleNs ≠ [])
    (input : Value (Sinsemilla.Chain.Inputs HashLayer.merkleNs.length) Fp)
    (wit : Sinsemilla.Chain.ChainWit HashLayer.merkleNs Fp) (hint : ProverHint Fp) :
    (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ hns).ProverAssumptions input wit hint
      = HashToPoint.ProverAssumptions G HashLayer.merkleNs Q input := rfl

private theorem hashC_proverSpec_eq (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : HashLayer.merkleNs ≠ [])
    (input : Value (Sinsemilla.Chain.Inputs HashLayer.merkleNs.length) Fp)
    (output : Value (HashToPoint.Output HashLayer.merkleNs.length) Fp)
    (wit : Sinsemilla.Chain.ChainWit HashLayer.merkleNs Fp) (hint : ProverHint Fp) :
    (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ hns).ProverSpec input output wit hint
      = HashToPoint.ProverSpec G HashLayer.merkleNs Q input output := rfl

/-- The suffix sum of bounded digits is the `pieceZ` of the recombined value (digit
canonicity: the value's `val` is the digit sum, and dividing by `2^K` drops the head). -/
private theorem sum_z1_eq_pieceZ {n : ℕ} (hn : K * (n + 1) ≤ 250) {ms : ℕ → ℕ}
    (hms : ∀ r, ms r < 2 ^ K)
    {p : Fp} (hp : p = ((∑ r ∈ Finset.range (n + 1), ms r * 2 ^ (K * r) : ℕ) : Fp)) :
    ((∑ j ∈ Finset.range n, ms (j + 1) * 2 ^ (K * j) : ℕ) : Fp) = pieceZ p 1 := by
  have hsum_lt : (∑ r ∈ Finset.range (n + 1), ms r * 2 ^ (K * r)) < 2 ^ (K * (n + 1)) :=
    sum_digits_lt hms (n + 1)
  have hlt_p : (∑ r ∈ Finset.range (n + 1), ms r * 2 ^ (K * r)) < PALLAS_BASE_CARD :=
    lt_trans (lt_of_lt_of_le hsum_lt (Nat.pow_le_pow_right (by norm_num) hn))
      two_pow_250_lt_p
  have hval : ZMod.val p = ∑ r ∈ Finset.range (n + 1), ms r * 2 ^ (K * r) := by
    rw [hp, ZMod.val_natCast_of_lt hlt_p]
  have hshift := sum_head_shift K n ms
  show _ = ((ZMod.val p / 2 ^ (K * 1) : ℕ) : Fp)
  rw [hval, hshift]
  congr 1
  rw [show K * 1 = K from by ring,
    Nat.add_mul_div_left (ms 0) _ (Nat.two_pow_pos K),
    Nat.div_eq_of_lt (hms 0)]
  omega

/-- The region count of `HashLayer.synthesize`: three witness-piece regions, two short
range checks, the hash region, the decomposition region = 7. -/
private theorem hashLayer_regionCount (G : Generators) (cfg : Config)
    (lcfg : Halo2.Ironwood.LookupRangeCheck.Config 10) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (input : Var HashLayer.Input Fp) (i : RegionIndex) :
    Operations.regionCount
      ((HashLayer.synthesize G cfg lcfg Q hQ l input).operations i) = 7 := by
  simp only [HashLayer.synthesize, HashToPoint.witnessMessagePiece,
    Halo2.Ironwood.LookupRangeCheck.witnessShortCheck, HashToPoint.hashMessage,
    Circuit.operations_bind, operations_assignRegion,
    Operations.regionCount_append, Operations.regionCount]
  rw [show ∀ (j : RegionIndex) (pieces : Var (Sinsemilla.Chain.Inputs
        HashLayer.merkleNs.length) Fp) (h1 : HashLayer.merkleNs ≠ []),
      Operations.regionCount
        (((HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ h1).call
          cfg.sinsemilla pieces).operations j) = 1 from fun j pieces h1 => by
    simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount,
      HashToPoint.hashCircuit, FormalRegionCircuit.toFormal]
    show Operations.regionCount ((assignRegion
        (HashToPoint.hashRegion G HashLayer.merkleNs Q hQ h1).name
        ((HashToPoint.hashRegion G HashLayer.merkleNs Q hQ h1).synthesize
          cfg.sinsemilla 0 pieces)).operations j) + 0 = 1
    rw [operations_assignRegion]
    simp only [Operations.regionCount]]
  simp only [Circuit.operations_pure, Operations.regionCount]

set_option linter.unusedSimpArgs false in
/-- One Merkle layer hash as a layouter-level formal circuit (Rust
`MerkleInstructions::hash_layer`, `merkle/chip.rs:229-436`), on the proven children
(`witnessShortCheck` ×2, the `hash_to_point` bundle, the decomposition `Gate`). -/
def HashLayer.circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ)
    (hl : l < 2 ^ 10) :
    FormalCircuit Fp (Config × Halo2.Ironwood.LookupRangeCheck.Config 10)
      (Config × Halo2.Ironwood.LookupRangeCheck.Config 10) HashLayer.Input field where
  name := "hash layer"
  configure := pure

  synthesize := fun (cfg, lcfg) input => HashLayer.synthesize G cfg lcfg Q hQ l input

  elaborated := fun (cfg, lcfg) =>
    { output := fun input i =>
        (HashLayer.synthesize G cfg lcfg Q hQ l input).output i
      regionCount := fun _ => 7
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i =>
        (hashLayer_regionCount G cfg lcfg Q hQ l input i).symm }

  EnvAssumptions := fun (cfg, lcfg) env =>
    Sinsemilla.GeneratorTableLoaded G cfg.sinsemilla.generatorTable env.env ∧
    Halo2.Ironwood.LookupRangeCheck.TableLoaded 10 lcfg env.env ∧
    lcfg.qLookup.index ≠ lcfg.qRunning.index

  Assumptions _ := True

  Spec input output _ := HashLayer.Spec G Q l input output ()

  ProverAssumptions input _ _ := HashLayer.ProverAssumptions G Q l input

  ProverSpec input output _ _ :=
    ∀ B, hashToPoint G.S Q
        (merkleChunks l (ZMod.val (show Fp from input.left))
          (ZMod.val (show Fp from input.right))) = some B →
      output = B.x

  soundness := by
    circuit_proof_start
    simp only [HashLayer.synthesize, HashToPoint.witnessMessagePiece,
      Halo2.Ironwood.LookupRangeCheck.witnessShortCheck, HashToPoint.hashMessage,
      circuit_norm] at hc
    subcircuit_rw at hc
    simp only [shortC_spec_eq, shortC_assumptions_eq, shortC_envAssumptions_eq,
      gateC_spec_eq, gateC_assumptions_eq, gateC_envAssumptions_eq,
      hashC_spec_eq, hashC_assumptions_eq, hashC_envAssumptions_eq] at hc
    obtain ⟨hB1, hB2, hHash, hGate⟩ := hc
    obtain ⟨hEgen, hEtab, hEdist⟩ := _hE
    have hAshort : (5 : ℕ) ≤ 10 ∧ 2 ^ 10 * 2 ^ 10 < PALLAS_BASE_CARD := by
      constructor
      · norm_num
      · norm_num [PALLAS_BASE_CARD]
    -- the eval of a positional cell is the raw advice read
    have hcellEval : ∀ (j : RegionIndex) (r : ℕ) (col : Column .advice),
        (eval (⟨place, env⟩ : Placed Environment Fp)
          (AssignedCell.of j r col : Var field Fp) : Fp)
        = env.advice col ((place j + r : ℕ) : ℤ) := fun _ _ _ => by
      with_unfolding_all rfl
    -- the b_1/b_2 range bounds (the shortcheck outputs ARE the gate's b_1/b_2 cells)
    have hb1 := hB1 ⟨hEtab, hEdist⟩ hAshort
    have hb2 := hB2 ⟨hEtab, hEdist⟩ hAshort
    rw [show (Halo2.Ironwood.LookupRangeCheck.shortRangeCheck 10 5).output cfg.2 0 () (i₀ + 1)
        = AssignedCell.of (i₀ + 1) 0 cfg.2.runningSum from rfl, hcellEval] at hb1
    rw [show (Halo2.Ironwood.LookupRangeCheck.shortRangeCheck 10 5).output cfg.2 0 () (i₀ + 2)
        = AssignedCell.of (i₀ + 2) 0 cfg.2.runningSum from rfl, hcellEval] at hb2
    -- the hash spec: chunking + running sums + the z1 view + the hash-from-Q contract
    have hHashS := hHash hEgen trivial
    rw [ProvableStruct.eval_cells_eq_eval, Sinsemilla.Chain.inputs_eval_literal] at hHashS
    rw [HashToPoint.hashCircuit_output_eval] at hHashS
    obtain ⟨chunks, hPC, hZs, hz1v, hContract⟩ := hHashS
    -- the gate spec on the landed cell values
    have hGateS := hGate trivial trivial
    simp only [HashToPoint.hashCircuit_output_z1s] at hGateS
    rw [gateInputs_eval_literal] at hGateS
    -- flatten every cell eval to raw advice reads
    simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
      Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
      Vector.getElem_ofFn] at hGateS hPC hb1 hb2
    -- land the running-sum extraction on the zsFam family and unpack the per-piece facts
    rw [show ((HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
          HashLayer.synthesize._proof_1).extract
          cfg.1.sinsemilla
          { pieces := #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
                         AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
                         AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces] }
          (i₀ + 3 + 2) { place := place, env := env }).zs
        = eval (⟨place, env⟩ : Placed Environment Fp)
            (Sinsemilla.Chain.zsCellsVal cfg.1.sinsemilla (i₀ + 3 + 2)
              HashLayer.merkleNs 0) from rfl,
      Sinsemilla.Chain.eval_zsCellsVal] at hZs
    rw [show HashLayer.merkleNs = 24 :: 1 :: 24 :: ([] : List ℕ) from rfl] at hZs
    obtain ⟨hzA, hzB, -⟩ := hZs
    simp only [Sinsemilla.Chain.zsFam_head] at hzA hzB
    have hzB' := (Sinsemilla.Chain.zsFam_tail_head
        (fun r => env.advice cfg.1.sinsemilla.bits
          ((place (i₀ + 3 + 2) + r : ℕ) : ℤ)) 24 1 [24] 0).symm.trans hzB
    -- the piece chunking at the concrete widths (`merkleNs` unfolds reducibly)
    obtain ⟨msA, hmsA, hpAval, tailB, hchunksEq, hPCB⟩ := hPC
    obtain ⟨msB, hmsB, hpBval, tailC, htailC, hPCC⟩ := hPCB
    obtain ⟨msC, hmsC, hpCval, tailN, htailN, hnil⟩ := hPCC
    rw [show ProvableType.eval (M := fields HashLayer.merkleNs.length) place env
        #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
           AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
           AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces]
      = #v[env.advice cfg.1.sinsemilla.witnessPieces ((place i₀ + 0 : ℕ) : ℤ),
           env.advice cfg.1.sinsemilla.witnessPieces
             ((place (i₀ + 1 + 2) + 0 : ℕ) : ℤ),
           env.advice cfg.1.sinsemilla.witnessPieces
             ((place (i₀ + 2 + 2) + 0 : ℕ) : ℤ)] from by
        with_unfolding_all rfl] at hpAval hpBval hpCval
    simp only [show ∀ (a b c : Fp), (#v[a, b, c] : Vector Fp 3)[0] = a from fun _ _ _ => rfl,
      show ∀ (a b c : Fp), (Vector.tail (#v[a, b, c] : Vector Fp 3))[0] = b
        from fun _ _ _ => rfl,
      show ∀ (a b c : Fp), (Vector.tail (Vector.tail (#v[a, b, c] : Vector Fp 3)))[0] = c
        from fun _ _ _ => rfl] at hpAval hpBval hpCval
    -- the z_1 values off the running-sum vectors, chunk-indexed through the append shape
    have hz1Aval := congrArg (fun v : Vector Fp 25 => v[1]'(by norm_num)) hzA
    have hz1Bval := congrArg (fun v : Vector Fp 2 => v[1]'(by norm_num)) hzB'
    simp only [Vector.getElem_ofFn] at hz1Aval hz1Bval
    -- normalize the row spellings across all facts
    simp only [show Sinsemilla.Chain.prefixRows HashLayer.merkleNs 0 = 0 from rfl,
      show Sinsemilla.Chain.prefixRows HashLayer.merkleNs 1 = 25 from rfl,
      Nat.add_zero, Nat.zero_add, show (24 + 1 + 1 : ℕ) = 26 from rfl]
      at hGateS hz1Aval hz1Bval hpAval hpBval hpCval hb1 hb2
    -- the chunk words through the append shape
    have hsumA : (∑ j ∈ Finset.range (24 + 1 - 1), chunks.getD (1 + j) 0 * 2 ^ (K * j))
        = ∑ j ∈ Finset.range 24, msA (j + 1) * 2 ^ (K * j) := by
      refine Finset.sum_congr (by norm_num) fun j hj => ?_
      rw [hchunksEq, Sinsemilla.Chain.chunks_head_getD msA tailB (1 + j)
        (by simp at hj; omega), Nat.add_comm 1 j]
    have hdrop : chunks.drop (24 + 1) = tailB := by
      rw [hchunksEq]
      exact Sinsemilla.Chain.chunks_drop_append msA tailB
    have hsumB : (∑ j ∈ Finset.range (1 + 1 - 1),
          (chunks.drop (24 + 1)).getD (1 + j) 0 * 2 ^ (K * j))
        = msB 1 := by
      rw [show (1 + 1 - 1) = 1 from rfl, Finset.sum_range_one, hdrop, htailC,
        Sinsemilla.Chain.chunks_head_getD msB tailC 1 (by norm_num)]
      norm_num
    rw [hsumA] at hz1Aval
    rw [hsumB] at hz1Bval
    -- the gate equations
    obtain ⟨hg1, hg2, hg3, hg4⟩ := hGateS
    dsimp only [] at hg1 hg2 hg3 hg4
    -- assemble the two node values
    have e10 : (twoPow10 : Fp) = (2 ^ 10 : Fp) := by norm_num [twoPow10]
    have e5 : (twoPow5 : Fp) = (2 ^ 5 : Fp) := by norm_num [twoPow5]
    have e240 : (twoPow240 : Fp) = (2 ^ 240 : Fp) := by norm_num [twoPow240]
    rw [show (24 + 1 : ℕ) = 25 from rfl] at hpAval
    rw [show (1 + 1 : ℕ) = 2 from rfl] at hpBval
    rw [show (24 + 1 : ℕ) = 25 from rfl] at hpCval
    rw [← e10] at hg1
    rw [← e10, ← e240] at hg2
    rw [← e5] at hg3
    rw [← e5] at hg4
    have hasm := assemble hmsA hmsB hmsC hl hb1 hb2
      hpAval hpBval hpCval
      (ZMod.natCast_zmod_val (env.advice cfg.2.runningSum
        ((place (i₀ + 1) : ℕ) : ℤ))).symm
      (ZMod.natCast_zmod_val (env.advice cfg.2.runningSum
        ((place (i₀ + 2) : ℕ) : ℤ))).symm
      hz1Aval hz1Bval hg1 hg2 hg3 hg4
    obtain ⟨lv, rv, hlv255, hrv255, hleftv, hrightv, hchunksM⟩ := hasm
    have hchunksIs : chunks = merkleChunks l lv rv := by
      rw [hchunksEq, htailC, htailN, hnil, hchunksM, List.append_nil]
    refine ⟨lv, rv, hlv255, hrv255, ?_, ?_, ?_⟩
    · show ((lv : ℕ) : Fp) = input_left
      rw [← h_input.1]
      exact hleftv
    · show ((rv : ℕ) : Fp) = input_right
      rw [← h_input.2]
      exact hrightv
    · intro B hB
      have hres := hContract B (by rw [hchunksIs]; exact hB)
      dsimp only [] at hres
      rw [show ((HashLayer.synthesize G cfg.1 cfg.2 Q hQ l
          { left := input_var_left, right := input_var_right }).output i₀)
        = AssignedCell.of (i₀ + 3 + 2)
            (0 + Sinsemilla.Chain.prefixRows HashLayer.merkleNs HashLayer.merkleNs.length)
            cfg.1.sinsemilla.xA from rfl] at h_output
      simp only [AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
        Cell.of_column, Environment.get_advice] at h_output
      rw [← h_output]
      exact hres.1

  completeness := by
    circuit_proof_start
    simp only [HashLayer.synthesize, HashToPoint.witnessMessagePiece,
      Halo2.Ironwood.LookupRangeCheck.witnessShortCheck, HashToPoint.hashMessage,
      circuit_norm] at hwit ⊢
    obtain ⟨hWa, ⟨hWb1x, hWb1⟩, ⟨hWb2x, hWb2⟩, hWb, hWc, hWhash, hWgate⟩ := hwit
    -- the canonical node values, the node reads, and the honest piece values
    obtain ⟨B0, hB0⟩ := hPA
    have hlv255 : ZMod.val input_left < 2 ^ 255 :=
      lt_trans (ZMod.val_lt _) p_lt_two_pow_255
    have hrv255 : ZMod.val input_right < 2 ^ 255 :=
      lt_trans (ZMod.val_lt _) p_lt_two_pow_255
    have hreadL : Sinsemilla.HashPiece.readCell ⟨place, env⟩ input_var_left
        = input_left := by
      rw [← h_input.1]
      with_unfolding_all rfl
    have hreadR : Sinsemilla.HashPiece.readCell ⟨place, env⟩ input_var_right
        = input_right := by
      rw [← h_input.2]
      with_unfolding_all rfl
    have hwaV : env.advice cfg.1.sinsemilla.witnessPieces ((place i₀ : ℕ) : ℤ)
        = ((l + 2 ^ 10 * bitrange (ZMod.val input_left) 0 240 : ℕ) : Fp) := by
      rw [hWa]
      simp only [HashLayer.waWit, Witgen.WitgenIROver.eval_native_apply, hreadL]
      rfl
    have hwbV : env.advice cfg.1.sinsemilla.witnessPieces
          ((place (i₀ + 1 + 2) : ℕ) : ℤ)
        = ((bitrange (ZMod.val input_left) 240 10
            + 2 ^ 10 * bitrange (ZMod.val input_left) 250 5
            + 2 ^ 15 * bitrange (ZMod.val input_right) 0 5 : ℕ) : Fp) := by
      rw [hWb]
      simp only [HashLayer.wbWit, Witgen.WitgenIROver.eval_native_apply, hreadL, hreadR]
      rfl
    have hwcV : env.advice cfg.1.sinsemilla.witnessPieces
          ((place (i₀ + 2 + 2) : ℕ) : ℤ)
        = ((bitrange (ZMod.val input_right) 5 250 : ℕ) : Fp) := by
      rw [hWc]
      simp only [HashLayer.wcWit, Witgen.WitgenIROver.eval_native_apply, hreadR]
      rfl
    have hhp := honest_pieces hl hlv255 hrv255 hwaV hwbV hwcV
    obtain ⟨⟨hbA, hbB, hbC⟩, hhchunks⟩ := hhp
    -- the hash child's honest-prover precondition (used by the leaf AND the derived run)
    have hPAhash : (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
        HashLayer.synthesize._proof_1).ProverAssumptions
        (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) ({ pieces := #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
            AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
            AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces] }
          : Var (Sinsemilla.Chain.Inputs HashLayer.merkleNs.length) Fp))
        ((HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
          HashLayer.synthesize._proof_1).extract
          cfg.1.sinsemilla
          { pieces := #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
              AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
              AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces] }
          (i₀ + 3 + 2) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)) env.hint := by
      rw [hashC_proverAssumptions_eq]
      rw [ProvableStruct.eval_cells_eq_eval_prover, Sinsemilla.Chain.inputs_eval_literal,
        show ProvableType.eval (M := fields HashLayer.merkleNs.length) place
          env.toEnvironment
          #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
             AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
             AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces]
        = #v[env.advice cfg.1.sinsemilla.witnessPieces ((place i₀ : ℕ) : ℤ),
             env.advice cfg.1.sinsemilla.witnessPieces
               ((place (i₀ + 1 + 2) : ℕ) : ℤ),
             env.advice cfg.1.sinsemilla.witnessPieces
               ((place (i₀ + 2 + 2) : ℕ) : ℤ)]
        from by with_unfolding_all rfl]
      refine ⟨by decide, ⟨?_, ?_, ?_, trivial⟩, B0, ?_⟩
      · show ZMod.val (env.advice cfg.1.sinsemilla.witnessPieces
          ((place i₀ : ℕ) : ℤ)) < 2 ^ (K * 25)
        exact hbA
      · show ZMod.val (env.advice cfg.1.sinsemilla.witnessPieces
          ((place (i₀ + 1 + 2) : ℕ) : ℤ)) < 2 ^ (K * 2)
        exact hbB
      · show ZMod.val (env.advice cfg.1.sinsemilla.witnessPieces
          ((place (i₀ + 2 + 2) : ℕ) : ℤ)) < 2 ^ (K * 25)
        exact hbC
      · show Orchard.Specs.Sinsemilla.hashToPoint G.S Q
          ((List.range 25).map (pieceWord (env.advice cfg.1.sinsemilla.witnessPieces
              ((place i₀ : ℕ) : ℤ)))
            ++ ((List.range 2).map (pieceWord (env.advice
                  cfg.1.sinsemilla.witnessPieces ((place (i₀ + 1 + 2) : ℕ) : ℤ)))
              ++ (List.range 25).map (pieceWord (env.advice
                  cfg.1.sinsemilla.witnessPieces ((place (i₀ + 2 + 2) : ℕ) : ℤ)))))
          = some B0
        rw [hhchunks]
        exact hB0
    -- the b_1/b_2 witnessed values, canonical
    have hb1V : env.advice cfg.2.runningSum ((place (i₀ + 1) : ℕ) : ℤ)
        = ((bitrange (ZMod.val input_left) 250 5 : ℕ) : Fp) := by
      rw [hWb1x]
      simp only [HashLayer.wb1Wit, Witgen.WitgenIROver.eval_native_apply, hreadL]
      rfl
    have hb2V : env.advice cfg.2.runningSum ((place (i₀ + 2) : ℕ) : ℤ)
        = ((bitrange (ZMod.val input_right) 0 5 : ℕ) : Fp) := by
      rw [hWb2x]
      simp only [HashLayer.wb2Wit, Witgen.WitgenIROver.eval_native_apply, hreadR]
      rfl
    -- the hash child's honest run: the verifier Spec (for the z_1 values) + the honest PS
    have hder := Halo2.SubcircuitRw.layouter_completeness_derived_placed
      (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
        HashLayer.synthesize._proof_1)
      cfg.1.sinsemilla (i₀ + 3 + 2) (⟨place, env⟩ : Placed ProverEnvironment Fp)
      { pieces := #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
          AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
          AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces] }
      hWhash _hE.1 trivial hPAhash
    obtain ⟨hSpecH, hPSH⟩ := hder
    rw [hashC_spec_eq] at hSpecH
    rw [hashC_proverSpec_eq] at hPSH
    rw [HashToPoint.hashCircuit_output_eval] at hSpecH
    obtain ⟨chunksH, hPCH, hZsH, -, -⟩ := hSpecH
    -- normalize the verifier-view spellings to the prover reads
    try simp only [Placed.toEnvironment_mk, Placed.toEnvironment_place, Placed.toEnvironment_env,
      ProverEnvironment.toEnvironment_advice] at hPCH hZsH
    -- the running-sum families and the z_1 sums (the soundness-side extraction)
    rw [show ((HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ
          HashLayer.synthesize._proof_1).extract
          cfg.1.sinsemilla
          { pieces := #v[AssignedCell.of i₀ 0 cfg.1.sinsemilla.witnessPieces,
              AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
              AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces] }
          (i₀ + 3 + 2) (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).zs
        = eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
            (Sinsemilla.Chain.zsCellsVal cfg.1.sinsemilla (i₀ + 3 + 2)
              HashLayer.merkleNs 0) from rfl,
      Sinsemilla.Chain.eval_zsCellsVal] at hZsH
    simp only [Placed.toEnvironment_mk, Placed.toEnvironment_place, Placed.toEnvironment_env] at hZsH
    rw [show HashLayer.merkleNs = 24 :: 1 :: 24 :: ([] : List ℕ) from rfl] at hZsH
    obtain ⟨hzAH, hzBH, -⟩ := hZsH
    simp only [Sinsemilla.Chain.zsFam_head] at hzAH
    have hzBH' := (Sinsemilla.Chain.zsFam_tail_head
        (fun r => env.advice cfg.1.sinsemilla.bits
          ((place (i₀ + 3 + 2) + r : ℕ) : ℤ)) 24 1 [24] 0).symm.trans hzBH
    obtain ⟨msA', hmsA', hpAval', tailB', hchunksEq', hPCB'⟩ := hPCH
    obtain ⟨msB', hmsB', hpBval', tailC', htailC', -⟩ := hPCB'
    have hpA2 : env.advice cfg.1.sinsemilla.witnessPieces ((place i₀ : ℕ) : ℤ)
        = ((∑ r ∈ Finset.range (24 + 1), msA' r * 2 ^ (K * r) : ℕ) : Fp) := by
      rw [← hpAval']
      with_unfolding_all rfl
    have hpB2 : env.advice cfg.1.sinsemilla.witnessPieces
          ((place (i₀ + 1 + 2) : ℕ) : ℤ)
        = ((∑ r ∈ Finset.range (1 + 1), msB' r * 2 ^ (K * r) : ℕ) : Fp) := by
      rw [← hpBval']
      with_unfolding_all rfl
    -- the z_1 cell values in `pieceZ` form (digit canonicity)
    have hz1AV := congrArg (fun v : Vector Fp 25 => v[1]'(by norm_num)) hzAH
    have hz1BV := congrArg (fun v : Vector Fp 2 => v[1]'(by norm_num)) hzBH'
    simp only [Vector.getElem_ofFn] at hz1AV hz1BV
    have hsumA' : (∑ j ∈ Finset.range (24 + 1 - 1), chunksH.getD (1 + j) 0 * 2 ^ (K * j))
        = ∑ j ∈ Finset.range 24, msA' (j + 1) * 2 ^ (K * j) := by
      refine Finset.sum_congr (by norm_num) fun j hj => ?_
      rw [hchunksEq', Sinsemilla.Chain.chunks_head_getD msA' tailB' (1 + j)
        (by simp at hj; omega), Nat.add_comm 1 j]
    have hsumB' : (∑ j ∈ Finset.range (1 + 1 - 1),
          (chunksH.drop (24 + 1)).getD (1 + j) 0 * 2 ^ (K * j))
        = msB' 1 := by
      rw [show (1 + 1 - 1) = 1 from rfl, Finset.sum_range_one,
        show chunksH.drop (24 + 1) = tailB' from by
          rw [hchunksEq']; exact Sinsemilla.Chain.chunks_drop_append msA' tailB',
        htailC', Sinsemilla.Chain.chunks_head_getD msB' tailC' 1 (by norm_num)]
      norm_num
    rw [hsumA'] at hz1AV
    rw [hsumB'] at hz1BV
    have hz1A_pieceZ : env.advice cfg.1.sinsemilla.bits
          ((place (i₀ + 3 + 2) + (0 + 1) : ℕ) : ℤ)
        = pieceZ (env.advice cfg.1.sinsemilla.witnessPieces
            ((place i₀ : ℕ) : ℤ)) 1 := by
      rw [hz1AV]
      exact sum_z1_eq_pieceZ (by norm_num [show K = 10 from rfl]) hmsA' hpA2
    have hz1B_pieceZ : env.advice cfg.1.sinsemilla.bits
          ((place (i₀ + 3 + 2) + (0 + (24 + 1) + 1) : ℕ) : ℤ)
        = pieceZ (env.advice cfg.1.sinsemilla.witnessPieces
            ((place (i₀ + 1 + 2) : ℕ) : ℤ)) 1 := by
      rw [hz1BV,
        show ((msB' 1 : ℕ) : Fp)
          = ((∑ j ∈ Finset.range 1, msB' (j + 1) * 2 ^ (K * j) : ℕ) : Fp) from by
          rw [Finset.sum_range_one]; norm_num]
      exact sum_z1_eq_pieceZ (by norm_num [show K = 10 from rfl]) hmsB' hpB2
    -- the gate spec on the honest values
    have hg := honest_gate hl hlv255 hrv255 hwaV hb1V hb2V hwbV hwcV
      hz1A_pieceZ hz1B_pieceZ (ZMod.natCast_zmod_val input_left)
      (ZMod.natCast_zmod_val input_right)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · -- b1 short check
      refine Halo2.SubcircuitRw.region_completeness_leaf_placed
        (Halo2.Ironwood.LookupRangeCheck.shortRangeCheck 10 5) cfg.2 0 (i₀ + 1) (⟨place, env⟩ : Placed ProverEnvironment Fp) ()
        hWb1 ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · exact _hE.2.1
      · exact _hE.2.2
      · exact ⟨by norm_num, by norm_num [PALLAS_BASE_CARD]⟩
      · rw [shortC_proverAssumptions_eq]
        simp only [Placed.toEnvironment_mk]
        rw [show ((Halo2.Ironwood.LookupRangeCheck.shortRangeCheck 10 5).extract
            cfg.2 0 () (i₀ + 1) (⟨place, env.toEnvironment⟩ : Placed Environment Fp) : Fp)
          = env.advice cfg.2.runningSum ((place (i₀ + 1) : ℕ) : ℤ) from by
            with_unfolding_all rfl, hWb1x]
        rw [show (Witgen.WitgenIROver.eval (HashLayer.wb1Wit input_var_left)
            { place := place, env := env })[0]
          = ((bitrange (Sinsemilla.HashPiece.readCell ⟨place, env⟩
              input_var_left).val 250 5 : ℕ) : Fp) from by
            simp only [HashLayer.wb1Wit, Witgen.WitgenIROver.eval_native_apply]
            rfl]
        show ZMod.val ((bitrange (Sinsemilla.HashPiece.readCell ⟨place, env⟩
            input_var_left).val 250 5 : ℕ) : Fp) < 2 ^ 5
        rw [ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ _ _) (by
          norm_num [PALLAS_BASE_CARD]))]
        exact bitrange_lt _ _ _
    · -- b2 short check
      refine Halo2.SubcircuitRw.region_completeness_leaf_placed
        (Halo2.Ironwood.LookupRangeCheck.shortRangeCheck 10 5) cfg.2 0 (i₀ + 2) (⟨place, env⟩ : Placed ProverEnvironment Fp) ()
        hWb2 ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · exact _hE.2.1
      · exact _hE.2.2
      · exact ⟨by norm_num, by norm_num [PALLAS_BASE_CARD]⟩
      · rw [shortC_proverAssumptions_eq]
        simp only [Placed.toEnvironment_mk]
        rw [show ((Halo2.Ironwood.LookupRangeCheck.shortRangeCheck 10 5).extract
            cfg.2 0 () (i₀ + 2) (⟨place, env.toEnvironment⟩ : Placed Environment Fp) : Fp)
          = env.advice cfg.2.runningSum ((place (i₀ + 2) : ℕ) : ℤ) from by
            with_unfolding_all rfl, hWb2x]
        rw [show (Witgen.WitgenIROver.eval (HashLayer.wb2Wit input_var_right)
            { place := place, env := env })[0]
          = ((bitrange (Sinsemilla.HashPiece.readCell ⟨place, env⟩
              input_var_right).val 0 5 : ℕ) : Fp) from by
            simp only [HashLayer.wb2Wit, Witgen.WitgenIROver.eval_native_apply]
            rfl]
        show ZMod.val ((bitrange (Sinsemilla.HashPiece.readCell ⟨place, env⟩
            input_var_right).val 0 5 : ℕ) : Fp) < 2 ^ 5
        rw [ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ _ _) (by
          norm_num [PALLAS_BASE_CARD]))]
        exact bitrange_lt _ _ _
    · -- the hash
      refine Halo2.SubcircuitRw.layouter_completeness_leaf_placed
        (HashToPoint.hashCircuit G HashLayer.merkleNs Q hQ HashLayer.synthesize._proof_1)
          cfg.1.sinsemilla (i₀ + 3 + 2) (⟨place, env⟩ : Placed ProverEnvironment Fp) _ hWhash
        ⟨?_, trivial, ?_⟩
      · exact _hE.1
      · exact hPAhash
    · -- the decomposition gate
      refine Halo2.SubcircuitRw.region_completeness_leaf_placed
        (Gate.circuit (l : Fp)) cfg.1.gate 0 _ (⟨place, env⟩ : Placed ProverEnvironment Fp) _ hWgate ⟨trivial, trivial, ?_⟩
      rw [gateC_proverAssumptions_eq]
      simp only [HashToPoint.hashCircuit_output_z1s]
      rw [gateInputs_eval_literal_prover]
      simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
        Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
        Vector.getElem_ofFn,
        show Sinsemilla.Chain.prefixRows HashLayer.merkleNs 0 = 0 from rfl,
        show Sinsemilla.Chain.prefixRows HashLayer.merkleNs 1 = 25 from rfl,
        Nat.add_zero, Nat.zero_add, show (25 + 1 : ℕ) = 26 from rfl]
      simp only [Nat.zero_add,
        show (24 + 1 + 1 : ℕ) = 26 from rfl,
        show (twoPow10 : Fp) = (2 ^ 10 : Fp) from by norm_num [twoPow10],
        show (twoPow5 : Fp) = (2 ^ 5 : Fp) from by norm_num [twoPow5],
        show (twoPow240 : Fp) = (2 ^ 240 : Fp) from by norm_num [twoPow240]] at hg
      rw [show Gate.GateSpec (↑l : Fp) = fun input => Gate.Spec input.aWhole input.bWhole
          input.cWhole input.leftNode input.rightNode input.z1A input.z1B input.b1
          input.b2 ↑l from rfl]
      dsimp only []
      rw [h_input.1, h_input.2]
      exact hg
    · -- the honest-prover contract
      intro B hB
      have hPSH' := hPSH B (by
        rw [show (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) ({ pieces := #v[AssignedCell.of i₀ 0
                  cfg.1.sinsemilla.witnessPieces,
                AssignedCell.of (i₀ + 1 + 2) 0 cfg.1.sinsemilla.witnessPieces,
                AssignedCell.of (i₀ + 2 + 2) 0 cfg.1.sinsemilla.witnessPieces] }
              : Var (Sinsemilla.Chain.Inputs HashLayer.merkleNs.length) Fp)
              : Value (Sinsemilla.Chain.Inputs HashLayer.merkleNs.length) Fp).pieces
          = #v[env.advice cfg.1.sinsemilla.witnessPieces ((place i₀ : ℕ) : ℤ),
               env.advice cfg.1.sinsemilla.witnessPieces
                 ((place (i₀ + 1 + 2) : ℕ) : ℤ),
               env.advice cfg.1.sinsemilla.witnessPieces
                 ((place (i₀ + 2 + 2) : ℕ) : ℤ)] from by with_unfolding_all rfl,
          show Sinsemilla.Chain.honestChunks HashLayer.merkleNs
            #v[env.advice cfg.1.sinsemilla.witnessPieces ((place i₀ : ℕ) : ℤ),
               env.advice cfg.1.sinsemilla.witnessPieces
                 ((place (i₀ + 1 + 2) : ℕ) : ℤ),
               env.advice cfg.1.sinsemilla.witnessPieces
                 ((place (i₀ + 2 + 2) : ℕ) : ℤ)]
          = (List.range 25).map (pieceWord (env.advice cfg.1.sinsemilla.witnessPieces
              ((place i₀ : ℕ) : ℤ)))
            ++ ((List.range 2).map (pieceWord (env.advice
                  cfg.1.sinsemilla.witnessPieces ((place (i₀ + 1 + 2) : ℕ) : ℤ)))
              ++ (List.range 25).map (pieceWord (env.advice
                  cfg.1.sinsemilla.witnessPieces ((place (i₀ + 2 + 2) : ℕ) : ℤ))))
          from by with_unfolding_all rfl, hhchunks]
        exact hB)
      rw [HashToPoint.hashCircuit_output_eval_prover] at hPSH'
      obtain ⟨hpx, -⟩ := hPSH'
      rw [show ((HashLayer.synthesize G cfg.1 cfg.2 Q hQ l
          { left := input_var_left, right := input_var_right }).output i₀)
        = AssignedCell.of (i₀ + 3 + 2)
            (0 + Sinsemilla.Chain.prefixRows HashLayer.merkleNs HashLayer.merkleNs.length)
            cfg.1.sinsemilla.xA from rfl] at h_output
      simp only [AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
        Cell.of_column, Environment.get_advice] at h_output
      rw [← h_output]
      exact hpx

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

/-- Chain two `MerkleRoot` segments. -/
theorem MerkleRoot.trans (G : Generators) (Q : Point Fp) {l a m r : _} {k k' : ℕ}
    (h1 : MerkleRoot G Q l a k m) (h2 : MerkleRoot G Q (l + k) m k' r) :
    MerkleRoot G Q l a (k + k') r := by
  induction k generalizing l a with
  | zero =>
    simp only [MerkleRoot] at h1
    subst h1
    simpa using h2
  | succ n ih =>
    obtain ⟨mid, hstep, hrest⟩ := h1
    rw [show n + 1 + k' = (n + k') + 1 from by omega, MerkleRoot]
    exact ⟨mid, hstep,
      ih hrest (by rwa [show l + 1 + n = l + (n + 1) from by omega])⟩

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

/-! ### `Layer` (CondSwap + HashLayer)

One Merkle path layer (`MerklePath::calculate_root`'s loop body): conditionally swap
`(node, sibling)` by the position bit — the sibling and the bit are prover witnesses
(Rust `Value`s) — then hash the swapped pair. Both children are proven
(`CondSwap.swap`, `HashLayer.circuit`). -/

/-- The swapped `(left, right)` pair a layer hashes, selected by the position bit. Donor
`Merkle.Layer.proverChunks` (value-level). -/
def proverChunks (l : ℕ) (node sibling : Fp) (posBit : Bool) : List ℕ :=
  merkleChunks l
    (ZMod.val (if posBit then sibling else node))
    (ZMod.val (if posBit then node else sibling))

namespace Layer

/-- The layer input: the running node cell (the sibling and position bit are witnesses). -/
structure Input (F : Type) where
  node : F
deriving ProvableStruct

end Layer

-- contract bridges for the layer's children (hand-written for the proof-typed binders)
private theorem hashLayerC_spec_eq (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) :
    (HashLayer.circuit G Q hQ l hl).Spec
      = fun input output _ => HashLayer.Spec G Q l input output () := rfl

private theorem hashLayerC_assumptions_eq (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) :
    (HashLayer.circuit G Q hQ l hl).Assumptions = fun _ => True := rfl

private theorem hashLayerC_envAssumptions_eq (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (cfg : Config × Halo2.Ironwood.LookupRangeCheck.Config 10)
    (env : Placed Environment Fp) :
    (HashLayer.circuit G Q hQ l hl).EnvAssumptions cfg env
      = (Sinsemilla.GeneratorTableLoaded G cfg.1.sinsemilla.generatorTable env.env ∧
        Halo2.Ironwood.LookupRangeCheck.TableLoaded 10 cfg.2 env.env ∧
        cfg.2.qLookup.index ≠ cfg.2.qRunning.index) := rfl

private theorem hashLayerC_proverAssumptions_eq (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (input : Value HashLayer.Input Fp) (wit : Value unit Fp) (hint : ProverHint Fp) :
    (HashLayer.circuit G Q hQ l hl).ProverAssumptions input wit hint
      = HashLayer.ProverAssumptions G Q l input := rfl

private theorem hashLayerC_proverSpec_eq (G : Generators) (Q : Point Fp)
    (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (input : Value HashLayer.Input Fp) (output : Value field Fp)
    (wit : Value unit Fp) (hint : ProverHint Fp) :
    (HashLayer.circuit G Q hQ l hl).ProverSpec input output wit hint
      = ∀ B, hashToPoint G.S Q (merkleChunks l (ZMod.val (show Fp from input.left))
          (ZMod.val (show Fp from input.right))) = some B → output = B.x := rfl

/-- The region count of the layer: the swap region + the hash layer's 7. -/
private theorem layer_regionCount (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool)
    (ccfg : CondSwap.Config) (cfg : Config)
    (lcfg : Halo2.Ironwood.LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let pair ← assignRegion "swap"
          ((Halo2.Ironwood.CondSwap.swap wsib wswap).call ccfg 0 { a := input.node })
        (HashLayer.circuit G Q hQ l hl).call (cfg, lcfg)
          { left := pair.aSwapped, right := pair.bSwapped }).operations i) = 8 := by
  simp only [Circuit.operations_bind, operations_assignRegion,
    Operations.regionCount_append, Operations.regionCount]
  rw [show ∀ (j : RegionIndex) (inp : Var HashLayer.Input Fp),
      Operations.regionCount
        (((HashLayer.circuit G Q hQ l hl).call (cfg, lcfg) inp).operations j) = 7
    from fun j inp => by
      simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount]
      rw [show ((HashLayer.circuit G Q hQ l hl).synthesize (cfg, lcfg) inp j).2.1
          = ((HashLayer.synthesize G cfg lcfg Q hQ l inp).operations j) from rfl]
      rw [hashLayer_regionCount G cfg lcfg Q hQ l inp j]]

/-- One Merkle path layer (the `MerklePath::calculate_root` loop body): conditionally swap
`(node, sibling)` by the position bit — sibling and bit are prover witness programs — then
the layer hash. `Spec` is `MerkleStep`. -/
def Layer.circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ)
    (hl : l < 2 ^ 10) (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool) :
    FormalCircuit Fp
      (CondSwap.Config × Config × Halo2.Ironwood.LookupRangeCheck.Config 10)
      (CondSwap.Config × Config × Halo2.Ironwood.LookupRangeCheck.Config 10)
      Layer.Input field where
  name := "MerkleCRH layer"
  configure := pure

  synthesize := fun (ccfg, cfg, lcfg) input => do
    let pair ← assignRegion "swap"
      ((Halo2.Ironwood.CondSwap.swap wsib wswap).call ccfg 0 { a := input.node })
    (HashLayer.circuit G Q hQ l hl).call (cfg, lcfg)
      { left := pair.aSwapped, right := pair.bSwapped }

  elaborated := fun (ccfg, cfg, lcfg) =>
    { output := fun input i =>
        ((do
          let pair ← assignRegion "swap"
            ((Halo2.Ironwood.CondSwap.swap wsib wswap).call ccfg 0 { a := input.node })
          (HashLayer.circuit G Q hQ l hl).call (cfg, lcfg)
            { left := pair.aSwapped, right := pair.bSwapped }
          : Circuit Fp (Var field Fp)).output i)
      regionCount := fun _ => 8
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i =>
        (layer_regionCount G Q hQ l hl wsib wswap ccfg cfg lcfg input i).symm }

  EnvAssumptions := fun (ccfg, cfg, lcfg) env =>
    Sinsemilla.GeneratorTableLoaded G cfg.sinsemilla.generatorTable env.env ∧
    Halo2.Ironwood.LookupRangeCheck.TableLoaded 10 lcfg env.env ∧
    lcfg.qLookup.index ≠ lcfg.qRunning.index

  Assumptions _ := True

  -- the swap witnesses (sibling, position flag), read off the swap region's cells
  Witness := fieldPair
  extract := fun (ccfg, _, _) _ i₀ env =>
    (eval env (AssignedCell.of i₀ 0 ccfg.b : Var field Fp),
     eval env (AssignedCell.of i₀ 0 ccfg.swap : Var field Fp))

  Spec input output _ := MerkleStep G Q l input.node output

  ProverAssumptions input wit _ :=
    ∃ B, hashToPoint G.S Q (proverChunks l input.node wit.1 (wit.2 = 1)) = some B

  ProverSpec input output wit _ :=
    ∀ B, hashToPoint G.S Q (proverChunks l input.node wit.1 (wit.2 = 1)) = some B →
      output = B.x

  soundness := by
    circuit_proof_start
    obtain ⟨hSwap, hHash⟩ := hc
    have hSw : Halo2.Ironwood.CondSwap.SwapSpec input_node
        (ProvableStruct.eval place env x_gen_out_0)
        ((Halo2.Ironwood.CondSwap.swap wsib wswap).extract cfg.1 0 { a := input_var_node }
          i₀ ⟨place, env⟩) := hSwap trivial trivial
    obtain ⟨hbool, hASw, hBSw⟩ := hSw
    -- the swapped cells' reads are the eval'd swap-output components
    have hAread : (env.get x_gen_out_0.aSwapped.cell.column
          ((place x_gen_out_0.aSwapped.cell.regionIndex
            + x_gen_out_0.aSwapped.cell.rowOffset : ℕ) : ℤ) : Fp)
        = (ProvableStruct.eval place env x_gen_out_0).aSwapped := by
      with_unfolding_all rfl
    have hBread : (env.get x_gen_out_0.bSwapped.cell.column
          ((place x_gen_out_0.bSwapped.cell.regionIndex
            + x_gen_out_0.bSwapped.cell.rowOffset : ℕ) : ℤ) : Fp)
        = (ProvableStruct.eval place env x_gen_out_0).bSwapped := by
      with_unfolding_all rfl
    have hHashS := hHash ⟨_hE.1, _hE.2.1, _hE.2.2⟩ trivial
    rw [hashLayerC_spec_eq] at hHashS
    obtain ⟨lv, rv, hlv, hrv, hleftEq, hrightEq, hcontract⟩ := hHashS
    rw [show ({ left := env.get x_gen_out_0.aSwapped.cell.column
                  ((place x_gen_out_0.aSwapped.cell.regionIndex
                    + x_gen_out_0.aSwapped.cell.rowOffset : ℕ) : ℤ),
                right := env.get x_gen_out_0.bSwapped.cell.column
                  ((place x_gen_out_0.bSwapped.cell.regionIndex
                    + x_gen_out_0.bSwapped.cell.rowOffset : ℕ) : ℤ) }
        : Value HashLayer.Input Fp).left
      = (env.get x_gen_out_0.aSwapped.cell.column
          ((place x_gen_out_0.aSwapped.cell.regionIndex
            + x_gen_out_0.aSwapped.cell.rowOffset : ℕ) : ℤ) : Fp) from rfl,
      hAread, hASw] at hleftEq
    rw [show ({ left := env.get x_gen_out_0.aSwapped.cell.column
                  ((place x_gen_out_0.aSwapped.cell.regionIndex
                    + x_gen_out_0.aSwapped.cell.rowOffset : ℕ) : ℤ),
                right := env.get x_gen_out_0.bSwapped.cell.column
                  ((place x_gen_out_0.bSwapped.cell.regionIndex
                    + x_gen_out_0.bSwapped.cell.rowOffset : ℕ) : ℤ) }
        : Value HashLayer.Input Fp).right
      = (env.get x_gen_out_0.bSwapped.cell.column
          ((place x_gen_out_0.bSwapped.cell.regionIndex
            + x_gen_out_0.bSwapped.cell.rowOffset : ℕ) : ℤ) : Fp) from rfl,
      hBread, hBSw] at hrightEq
    refine ⟨lv, rv, hlv, hrv, ?_, hcontract⟩
    rcases hbool with h0 | h1
    · rw [if_neg (show ¬ _ = (1 : Fp) from by rw [h0]; decide)] at hleftEq
      exact Or.inl hleftEq
    · rw [if_pos h1] at hrightEq
      exact Or.inr hrightEq

  completeness := by
    circuit_proof_start
    obtain ⟨B0, hB0⟩ := hPA
    -- the swap child's honest values (its ProverSpec, over the witness-cell reads)
    have hSwPS := h_spec_0 trivial trivial trivial
    have hwit1 : ((Halo2.Ironwood.CondSwap.swap wsib wswap).extract cfg.1 0
          { a := input_var_node } i₀ (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).1
        = env.advice cfg.1.b ((place i₀ : ℕ) : ℤ) := by
      with_unfolding_all rfl
    have hwit2 : ((Halo2.Ironwood.CondSwap.swap wsib wswap).extract cfg.1 0
          { a := input_var_node } i₀ (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).2
        = env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) := by
      with_unfolding_all rfl
    obtain ⟨-, hASw, hBSw⟩ := hSwPS
    rw [hwit1, hwit2, h_input] at hASw hBSw
    -- the swapped cells' reads are the eval'd swap-output components
    have hAread : (env.get x_gen_out_0.aSwapped.cell.column
          ((place x_gen_out_0.aSwapped.cell.regionIndex
            + x_gen_out_0.aSwapped.cell.rowOffset : ℕ) : ℤ) : Fp)
        = (ProvableStruct.eval place env.toEnvironment x_gen_out_0).aSwapped := by
      with_unfolding_all rfl
    have hBread : (env.get x_gen_out_0.bSwapped.cell.column
          ((place x_gen_out_0.bSwapped.cell.regionIndex
            + x_gen_out_0.bSwapped.cell.rowOffset : ℕ) : ℤ) : Fp)
        = (ProvableStruct.eval place env.toEnvironment x_gen_out_0).bSwapped := by
      with_unfolding_all rfl
    -- the hash child's honest-prover precondition
    have hPAhash : (HashLayer.circuit G Q hQ l hl).ProverAssumptions
        { left := env.get x_gen_out_0.aSwapped.cell.column
            ((place x_gen_out_0.aSwapped.cell.regionIndex
              + x_gen_out_0.aSwapped.cell.rowOffset : ℕ) : ℤ),
          right := env.get x_gen_out_0.bSwapped.cell.column
            ((place x_gen_out_0.bSwapped.cell.regionIndex
              + x_gen_out_0.bSwapped.cell.rowOffset : ℕ) : ℤ) }
        ((HashLayer.circuit G Q hQ l hl).extract (cfg.2.1, cfg.2.2)
          { left := x_gen_out_0.aSwapped, right := x_gen_out_0.bSwapped } (i₀ + 1)
          (⟨place, env.toEnvironment⟩ : Placed Environment Fp)) env.hint := by
      rw [hashLayerC_proverAssumptions_eq]
      refine ⟨B0, ?_⟩
      show hashToPoint G.S Q (merkleChunks l
          (ZMod.val (env.get x_gen_out_0.aSwapped.cell.column
            ((place x_gen_out_0.aSwapped.cell.regionIndex
              + x_gen_out_0.aSwapped.cell.rowOffset : ℕ) : ℤ)))
          (ZMod.val (env.get x_gen_out_0.bSwapped.cell.column
            ((place x_gen_out_0.bSwapped.cell.regionIndex
              + x_gen_out_0.bSwapped.cell.rowOffset : ℕ) : ℤ)))) = some B0
      rw [hAread, hBread, hASw, hBSw]
      by_cases hs : env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) = 1
      · rw [if_pos hs, if_pos hs]
        rw [show decide (env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) = 1)
            = true from by simp [hs]] at hB0
        simpa [proverChunks] using hB0
      · rw [if_neg hs, if_neg hs]
        rw [show decide (env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) = 1)
            = false from by simp [hs]] at hB0
        simpa [proverChunks] using hB0
    refine ⟨⟨⟨trivial, trivial, trivial⟩, ⟨_hE.1, _hE.2.1, _hE.2.2⟩, trivial, hPAhash⟩, ?_⟩
    -- the honest-prover contract
    intro B hB
    have hPShash := (h_spec_1 ⟨_hE.1, _hE.2.1, _hE.2.2⟩ trivial hPAhash).2
    rw [hashLayerC_proverSpec_eq] at hPShash
    have hres := hPShash B (by
      show hashToPoint G.S Q (merkleChunks l
          (ZMod.val (env.get x_gen_out_0.aSwapped.cell.column
            ((place x_gen_out_0.aSwapped.cell.regionIndex
              + x_gen_out_0.aSwapped.cell.rowOffset : ℕ) : ℤ)))
          (ZMod.val (env.get x_gen_out_0.bSwapped.cell.column
            ((place x_gen_out_0.bSwapped.cell.regionIndex
              + x_gen_out_0.bSwapped.cell.rowOffset : ℕ) : ℤ)))) = some B
      rw [hAread, hBread, hASw, hBSw]
      by_cases hs : env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) = 1
      · rw [if_pos hs, if_pos hs]
        rw [show decide (env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) = 1)
            = true from by simp [hs]] at hB
        simpa [proverChunks] using hB
      · rw [if_neg hs, if_neg hs]
        rw [show decide (env.advice cfg.1.swap ((place i₀ : ℕ) : ℤ) = 1)
            = false from by simp [hs]] at hB
        simpa [proverChunks] using hB)
    rw [← h_output]
    exact hres

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

/-! #### The 32-layer fold (`MerklePath::calculate_root`), on `FormalCircuit.foldCall` -/

/-- The layer family: layer `i` is `Layer.circuit` at `l = i` (`% 2 ^ 10` totalizer —
identity on the 32 layers used). -/
def layerAt (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l₀ : ℕ)
    (wsib : ℕ → WitgenIR Fp 1) (wswap : ℕ → Placed ProverEnvironment Fp → Bool) (i : ℕ) :
    FormalCircuit Fp
      (CondSwap.Config × Config × Halo2.Ironwood.LookupRangeCheck.Config 10)
      (CondSwap.Config × Config × Halo2.Ironwood.LookupRangeCheck.Config 10)
      Layer.Input field :=
  Layer.circuit G Q hQ ((l₀ + i) % 2 ^ 10) (Nat.mod_lt _ (by norm_num)) (wsib i) (wswap i)

/-- Feed a layer's root cell back as the next layer's node. -/
def toInput : Var field Fp → Var Layer.Input Fp := fun out => { node := out }

/-- The running node over the *extracted* per-layer `(sibling, swap)` readings (`none` once a
layer hash is undefined) — the fold's own honest-node chain. The honest-input instantiation
(path/pos witness programs) recovers `honestNode`. -/
def pathNode (G : Generators) (Q : Point Fp) (l₀ : ℕ) (wit : ℕ → Fp × Fp) (node : Fp) :
    ℕ → Option Fp
  | 0 => some node
  | k + 1 => (pathNode G Q l₀ wit node k).bind fun n =>
      (hashToPoint G.S Q (proverChunks (l₀ + k) n (wit k).1 ((wit k).2 = 1))).map (·.x)

/-- `pathNode` only reads the witness below the depth. -/
theorem pathNode_congr (G : Generators) (Q : Point Fp) (l₀ : ℕ)
    {w w' : ℕ → Fp × Fp} (node : Fp) (k : ℕ) (h : ∀ j, j < k → w j = w' j) :
    pathNode G Q l₀ w node k = pathNode G Q l₀ w' node k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [pathNode, pathNode, ih (fun j hj => h j (by omega)), h n (by omega)]

theorem pathNode_isSome_of_succ (G : Generators) (Q : Point Fp) (l₀ : ℕ) (wit : ℕ → Fp × Fp)
    (node : Fp) (k : ℕ) (h : (pathNode G Q l₀ wit node (k + 1)).isSome) :
    (pathNode G Q l₀ wit node k).isSome := by
  rw [pathNode] at h
  rcases hb : pathNode G Q l₀ wit node k with _ | v
  · rw [hb] at h; simp at h
  · simp

theorem pathNode_isSome_le (G : Generators) (Q : Point Fp) (l₀ : ℕ) (wit : ℕ → Fp × Fp)
    (node : Fp) {i j : ℕ} (hij : i ≤ j) (h : (pathNode G Q l₀ wit node j).isSome) :
    (pathNode G Q l₀ wit node i).isSome := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]; exact h
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · exact ih (by omega) (pathNode_isSome_of_succ G Q l₀ wit node m h)
    · have : i = m + 1 := by omega
      rwa [this]

variable (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l₀ d : ℕ)
  (hld : l₀ + d ≤ 2 ^ 10)
  (wsib : ℕ → WitgenIR Fp 1) (wswap : ℕ → Placed ProverEnvironment Fp → Bool)

/-- The fold's region index entering layer `m`: 8 regions per layer. -/
private theorem foldState_snd
    (cfg : CondSwap.Config × Config × Halo2.Ironwood.LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (i₀ : RegionIndex) : ∀ m : ℕ,
    (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg input i₀ m).2
      = i₀ + 8 * m
  | 0 => rfl
  | m + 1 => by
    show (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg input i₀ m).2 + 8
      = i₀ + 8 * (m + 1)
    rw [foldState_snd cfg input i₀ m, Nat.mul_succ, Nat.add_assoc]

/-- The fold's region count: `8 * d`. -/
private theorem fold_regionCount
    (cfg : CondSwap.Config × Config × Halo2.Ironwood.LookupRangeCheck.Config 10)
    (input : Var Layer.Input Fp) (i : RegionIndex) :
    Operations.regionCount
      (((FormalCircuit.foldCall (layerAt G Q hQ l₀ wsib wswap) toInput cfg input d >>=
        fun acc => pure acc.node) : Circuit Fp (Var field Fp)).operations i)
      = 8 * d := by
  have h := FormalCircuit.foldOps_regionCount (layerAt G Q hQ l₀ wsib wswap) toInput cfg input
    i d
  rw [foldState_snd G Q hQ l₀ wsib wswap cfg input i d] at h
  simp only [Circuit.operations_bind, Circuit.operations_pure,
    FormalCircuit.foldCall_operations, Operations.regionCount_append, Operations.regionCount]
  rw [Nat.add_zero]
  exact Nat.add_left_cancel h

/-- Projection landing: `.node` of an eval'd `Layer.Input` var is the eval of its cell. -/
private theorem input_eval_node (env : Placed Environment Fp) (v : Var Layer.Input Fp) :
    (eval env v : Value Layer.Input Fp).node = (eval env v.node : Fp) := by
  rw [ProvableStruct.eval_cells_eq_eval]
  with_unfolding_all rfl

private theorem input_eval_node_prover (env : Placed ProverEnvironment Fp)
    (v : Var Layer.Input Fp) :
    (eval env v : Value Layer.Input Fp).node = (eval env v.node : Fp) := by
  rw [ProvableStruct.eval_cells_eq_eval_prover]
  with_unfolding_all rfl

/-- Rust `MerklePath::calculate_root` (`merkle.rs`): the 32-layer serial fold of
`Layer.circuit` (layer `i` at `l = i`), fed by the per-layer sibling/position-bit witness
programs. `Spec` is `MerkleRoot` over the leaf. -/
def circuit :
    FormalCircuit Fp
      (CondSwap.Config × Config × Halo2.Ironwood.LookupRangeCheck.Config 10)
      (CondSwap.Config × Config × Halo2.Ironwood.LookupRangeCheck.Config 10)
      Layer.Input field where
  name := "MerkleCRH calculate_root"
  configure := pure

  synthesize cfg input := do
    let acc ← FormalCircuit.foldCall (layerAt G Q hQ l₀ wsib wswap) toInput cfg input d
    pure acc.node

  elaborated cfg :=
    { output := fun input i =>
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg input i d).1.node
      regionCount := fun _ => 8 * d
      output_eq := by
        intro input i
        symm
        show (FormalCircuit.foldCall (layerAt G Q hQ l₀ wsib wswap) toInput cfg input d >>=
          fun acc => pure acc.node).output i = _
        rw [Circuit.output_bind, FormalCircuit.foldCall_output]
        rfl
      regionCount_eq := fun input i =>
        (fold_regionCount G Q hQ l₀ d wsib wswap cfg input i).symm }

  EnvAssumptions := fun (_, cfg, lcfg) env =>
    Sinsemilla.GeneratorTableLoaded G cfg.sinsemilla.generatorTable env.env ∧
    Halo2.Ironwood.LookupRangeCheck.TableLoaded 10 lcfg env.env ∧
    lcfg.qLookup.index ≠ lcfg.qRunning.index

  Assumptions _ := True

  -- the 32 per-layer (sibling, swap) cell readings, at 8-region stride
  Witness := fun F => ℕ → F × F
  extract := fun (ccfg, _, _) _ i₀ env => fun j =>
    (eval env (AssignedCell.of (i₀ + 8 * j) 0 ccfg.b : Var field Fp),
     eval env (AssignedCell.of (i₀ + 8 * j) 0 ccfg.swap : Var field Fp))

  Spec input output _ := MerkleRoot G Q l₀ input.node d output

  ProverAssumptions input wit _ := (pathNode G Q l₀ wit input.node d).isSome

  -- the honest output is the running `pathNode` value (exported so a parent can chain
  -- a second fold from this fold's output cell)
  ProverSpec input output wit _ :=
    ∀ n, pathNode G Q l₀ wit (input.node : Fp) d = some n → (output : Fp) = n

  soundness := by
    circuit_proof_start
    rw [FormalCircuit.foldCall_operations, FormalCircuit.foldOps_constraints] at hc
    subcircuit_rw at hc
    -- the per-layer contract, `l = i`
    have hstep : ∀ i : Fin d, MerkleStep G Q (l₀ + ↑i)
        ((eval (⟨place, env⟩ : Placed Environment Fp)
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
            { node := input_var_node } i₀ ↑i).1 : Value Layer.Input Fp).node)
        (eval (⟨place, env⟩ : Placed Environment Fp)
          ((layerAt G Q hQ l₀ wsib wswap ↑i).output cfg
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
              { node := input_var_node } i₀ ↑i).1
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
              { node := input_var_node } i₀ ↑i).2)) := by
      intro i
      have h : MerkleStep G Q ((l₀ + ↑i) % 2 ^ 10)
          ((eval (⟨place, env⟩ : Placed Environment Fp)
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
              { node := input_var_node } i₀ ↑i).1 : Value Layer.Input Fp).node)
          (eval (⟨place, env⟩ : Placed Environment Fp)
            ((layerAt G Q hQ l₀ wsib wswap ↑i).output cfg
              (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
                { node := input_var_node } i₀ ↑i).1
              (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
                { node := input_var_node } i₀ ↑i).2)) :=
        hc i ⟨_hE.1, _hE.2.1, _hE.2.2⟩ trivial
      rwa [Nat.mod_eq_of_lt (show l₀ + (↑i : ℕ) < 2 ^ 10 from by
        have := i.isLt; omega)] at h
    -- assemble the step chain into the root
    have hroot := merkleRoot_of_steps G Q
      (fun k => (eval (⟨place, env⟩ : Placed Environment Fp)
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1 : Value Layer.Input Fp).node) l₀ d
      (fun i hi => by
        have h := hstep ⟨i, hi⟩
        show MerkleStep G Q (l₀ + i)
          ((eval (⟨place, env⟩ : Placed Environment Fp)
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
              { node := input_var_node } i₀ i).1 : Value Layer.Input Fp).node)
          ((eval (⟨place, env⟩ : Placed Environment Fp)
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
              { node := input_var_node } i₀ (i + 1)).1 : Value Layer.Input Fp).node)
        rw [show (eval (⟨place, env⟩ : Placed Environment Fp)
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
              { node := input_var_node } i₀ (i + 1)).1 : Value Layer.Input Fp).node
          = eval (⟨place, env⟩ : Placed Environment Fp)
            ((layerAt G Q hQ l₀ wsib wswap i).output cfg
              (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
                { node := input_var_node } i₀ i).1
              (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
                { node := input_var_node } i₀ i).2) from by
          rw [show (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
              { node := input_var_node } i₀ (i + 1)).1
            = toInput ((layerAt G Q hQ l₀ wsib wswap i).output cfg
              (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
                { node := input_var_node } i₀ i).1
              (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
                { node := input_var_node } i₀ i).2) from rfl]
          rw [input_eval_node]
          rfl]
        exact h)
    -- land the endpoints
    have hf0 : (eval (⟨place, env⟩ : Placed Environment Fp)
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ 0).1 : Value Layer.Input Fp).node = input_node := by
      rw [show (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ 0).1
        = ({ node := input_var_node } : Var Layer.Input Fp) from rfl]
      rw [input_eval_node]
      rw [show (eval (⟨place, env⟩ : Placed Environment Fp)
          (({ node := input_var_node } : Var Layer.Input Fp).node) : Fp)
        = env.get input_var_node.cell.column
          ((place input_var_node.cell.regionIndex
            + input_var_node.cell.rowOffset : ℕ) : ℤ) from by with_unfolding_all rfl]
      exact h_input
    have hfd : (eval (⟨place, env⟩ : Placed Environment Fp)
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ d).1 : Value Layer.Input Fp).node = output := by
      rw [input_eval_node]
      rw [show (eval (⟨place, env⟩ : Placed Environment Fp)
          ((FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
            { node := input_var_node } i₀ d).1.node) : Fp)
        = env.get (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
            { node := input_var_node } i₀ d).1.node.cell.column
          ((place (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
              { node := input_var_node } i₀ d).1.node.cell.regionIndex
            + (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
              { node := input_var_node } i₀ d).1.node.cell.rowOffset : ℕ) : ℤ)
          from by with_unfolding_all rfl]
      exact h_output
    rw [← hf0, ← hfd]
    exact hroot

  completeness := by
    circuit_proof_start
    rw [FormalCircuit.foldCall_operations, FormalCircuit.foldOps_extendsWitnesses] at hwit
    set w : ℕ → Fp × Fp := fun j =>
      (env.advice cfg.1.b ((place (i₀ + 8 * j) : ℕ) : ℤ),
       env.advice cfg.1.swap ((place (i₀ + 8 * j) : ℕ) : ℤ)) with hw_def
    -- the per-layer extract readings ARE `w`
    have hext : ∀ k : ℕ, (layerAt G Q hQ l₀ wsib wswap k).extract cfg
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
        (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env⟩ : Placed Environment Fp)
        = w k := by
      intro k
      rw [foldState_snd G Q hQ l₀ wsib wswap cfg { node := input_var_node } i₀ k]
      with_unfolding_all rfl
    -- accumulator step landing (prover view)
    have hnodeS : ∀ k : ℕ,
        (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ (k + 1)).1 : Value Layer.Input Fp).node
        = (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) ((layerAt G Q hQ l₀ wsib wswap k).output cfg
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2) : Fp) := by
      intro k
      rw [show (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ (k + 1)).1
        = toInput ((layerAt G Q hQ l₀ wsib wswap k).output cfg
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2) from rfl]
      rw [input_eval_node_prover]
      rfl
    -- the honest running node lands on the accumulator, layer by layer
    have hmain : ∀ k : ℕ, k ≤ d →
        ∀ n, pathNode G Q l₀ w input_node k = some n →
        (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1 : Value Layer.Input Fp).node = n := by
      intro k
      induction k with
      | zero =>
        intro _ n hn
        simp only [pathNode, Option.some.injEq] at hn
        rw [show (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ 0).1
          = ({ node := input_var_node } : Var Layer.Input Fp) from rfl]
        rw [input_eval_node_prover]
        rw [show (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (({ node := input_var_node } : Var Layer.Input Fp).node) : Fp)
          = env.get input_var_node.cell.column
            ((place input_var_node.cell.regionIndex
              + input_var_node.cell.rowOffset : ℕ) : ℤ) from by with_unfolding_all rfl]
        rw [← hn]
        exact h_input
      | succ k ih =>
        intro hk n hn
        rw [pathNode] at hn
        rcases hpk : pathNode G Q l₀ w input_node k with _ | nk
        · rw [hpk] at hn; simp at hn
        rw [hpk] at hn
        simp only [Option.bind_some] at hn
        rcases hB : hashToPoint G.S Q (proverChunks (l₀ + k) nk (w k).1 ((w k).2 = 1)) with _ | B
        · rw [hB] at hn; simp at hn
        rw [hB] at hn
        simp only [Option.map_some, Option.some.injEq] at hn
        -- layer k's honest-prover precondition
        have hPAk : (layerAt G Q hQ l₀ wsib wswap k).ProverAssumptions
            (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1)
            ((layerAt G Q hQ l₀ wsib wswap k).extract cfg
              (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
              (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp))
            env.hint := by
          show ∃ B', hashToPoint G.S Q (proverChunks ((l₀ + k) % 2 ^ 10)
              ((eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1 : Value Layer.Input Fp).node)
              ((layerAt G Q hQ l₀ wsib wswap k).extract cfg
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).1
              (((layerAt G Q hQ l₀ wsib wswap k).extract cfg
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).2 = 1)) = some B'
          rw [hext k, ih (by omega) nk hpk,
            Nat.mod_eq_of_lt (show l₀ + k < 2 ^ 10 from by omega)]
          exact ⟨B, hB⟩
        -- layer k's honest contract: the output cell is the layer hash
        have hd := SubcircuitRw.layouter_completeness_derived_placed (layerAt G Q hQ l₀ wsib wswap k) cfg
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env⟩ : Placed ProverEnvironment Fp)
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
          (hwit ⟨k, Nat.lt_of_succ_le hk⟩) ⟨_hE.1, _hE.2.1, _hE.2.2⟩ trivial hPAk
        have hps : (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) ((layerAt G Q hQ l₀ wsib wswap k).output cfg
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
            (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2) : Fp) = B.x := by
          refine (show ∀ B' : Point Fp, hashToPoint G.S Q (proverChunks ((l₀ + k) % 2 ^ 10)
              ((eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1 : Value Layer.Input Fp).node)
              ((layerAt G Q hQ l₀ wsib wswap k).extract cfg
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).1
              (((layerAt G Q hQ l₀ wsib wswap k).extract cfg
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).2 = 1)) = some B' →
              (eval (⟨place, env⟩ : Placed ProverEnvironment Fp) ((layerAt G Q hQ l₀ wsib wswap k).output cfg
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).1
                (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ k).2) : Fp) = B'.x from hd.2) B ?_
          rw [hext k, ih (by omega) nk hpk,
            Nat.mod_eq_of_lt (show l₀ + k < 2 ^ 10 from by omega)]
          exact hB
        rw [hnodeS k, hps, hn]
    -- the honest-output landing (the strengthened `ProverSpec`), then the constraints
    refine ⟨?_, fun n hn => h_output.symm.trans
      (by with_unfolding_all exact hmain d (Nat.le_refl d) n hn)⟩
    rw [FormalCircuit.foldCall_operations, FormalCircuit.foldOps_constraints]
    -- discharge each layer's chunk
    intro i
    have hs := pathNode_isSome_le G Q l₀ w input_node
      (show (↑i + 1 : ℕ) ≤ d from i.isLt) hPA
    rw [pathNode] at hs
    rcases hpk : pathNode G Q l₀ w input_node ↑i with _ | nk
    · rw [hpk] at hs; simp at hs
    rw [hpk] at hs
    simp only [Option.bind_some] at hs
    rcases hB : hashToPoint G.S Q (proverChunks (l₀ + ↑i) nk (w ↑i).1 ((w ↑i).2 = 1)) with _ | B
    · rw [hB] at hs; simp at hs
    refine SubcircuitRw.layouter_completeness_leaf_placed (layerAt G Q hQ l₀ wsib wswap ↑i) cfg
      (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).2 (⟨place, env⟩ : Placed ProverEnvironment Fp)
      (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).1
      (hwit i) ⟨⟨_hE.1, _hE.2.1, _hE.2.2⟩, trivial, ?_⟩
    show ∃ B', hashToPoint G.S Q (proverChunks ((l₀ + ↑i) % 2 ^ 10)
        ((eval (⟨place, env⟩ : Placed ProverEnvironment Fp) (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).1 : Value Layer.Input Fp).node)
        ((layerAt G Q hQ l₀ wsib wswap ↑i).extract cfg
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).1
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).1
        (((layerAt G Q hQ l₀ wsib wswap ↑i).extract cfg
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).1
          (FormalCircuit.foldState (layerAt G Q hQ l₀ wsib wswap) toInput cfg
          { node := input_var_node } i₀ ↑i).2 (⟨place, env.toEnvironment⟩ : Placed Environment Fp)).2 = 1)) = some B'
    rw [hext ↑i, hmain ↑i (Nat.le_of_lt i.isLt) nk hpk,
      Nat.mod_eq_of_lt (show l₀ + (↑i : ℕ) < 2 ^ 10 from by
        have := i.isLt; omega)]
    exact ⟨B, hB⟩

end CalculateRoot

end Halo2.Ironwood.Sinsemilla.Merkle
