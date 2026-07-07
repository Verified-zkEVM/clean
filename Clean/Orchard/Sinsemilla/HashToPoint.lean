import Batteries.Data.Vector.Lemmas
import Clean.Orchard.Sinsemilla.Chip
import Clean.Orchard.Ecc.DoubleAndAdd
import Clean.Orchard.Specs.Sinsemilla
import Clean.Orchard.Ecc.AddIncomplete
import Clean.Orchard.Sinsemilla.HVec

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/chip/generator_table.rs`
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`

The generator table holds the `2^K` Sinsemilla generators
`(table_idx, table_x, table_y) = (j, S(j).x, S(j).y)`. Every `q_sinsemilla1` row of
`hash_to_point` looks up its message word `m`, its generator `x`-coordinate `x_p`, and
the derived generator `y`-coordinate
`y_p = Y_A/2 - λ₁·(x_A - x_P)` in this table.
-/

namespace Orchard.Sinsemilla

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Specs.Sinsemilla (Generators)
open Specs (K)
open Chip
open Ecc

/-- One row of the Sinsemilla generator table:
`(table_idx, table_x, table_y)`. -/
structure GeneratorTableRow (F : Type) where
  idx : F
  x : F
  y : F
deriving ProvableStruct

/-- The `2^K`-entry generator lookup table `(j, S(j).x, S(j).y)`. -/
def generatorTable (G : Generators) : Table Fp GeneratorTableRow := .fromStatic {
  name := "sinsemilla generators"
  length := 2 ^ K
  row i := { idx := (i.val : Fp), x := (G.S i.val).x, y := (G.S i.val).y }
  index r := r.idx.val
  Spec r := ∃ m : ℕ, m < 2 ^ K ∧
    r.idx = (m : Fp) ∧ r.x = (G.S m).x ∧ r.y = (G.S m).y
  contains_iff := by
    intro r
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.is_lt, rfl, rfl, rfl⟩
    · rintro ⟨m, hm, hidx, hx, hy⟩
      refine ⟨⟨m, hm⟩, ?_⟩
      obtain ⟨ridx, rx, ry⟩ := r
      simp only [GeneratorTableRow.mk.injEq]
      exact ⟨hidx, hx, hy⟩
}

/-!
### Hash piece

`hash_to_point.rs::hash_piece`: hashing one message piece of `w + 1` words. The piece
value is copied into the running sum `z_0`, decomposed word by word, and each word's
generator is accumulated with two incomplete additions encoded by one gate row.

The accumulator `y`-coordinate is not a cell: rows carry it as the derived expression
`Y_A = (λ₁ + λ₂)·(x_A - x_R)` (twice the `y`-coordinate), and the prover threads its
value as a hint (halo2's `Y<pallas::Base>` wrapper around `Value`). The gates linking a
piece to its successor (and the initial `y_Q` gate) reference rows of both pieces, so
they are emitted by the composing circuit, not here.
-/

/-- The honest word value `r` of a message piece (`K`-bit chunks, little-endian). -/
def pieceWord (p : Fp) (r : ℕ) : ℕ := p.val / 2 ^ (K * r) % 2 ^ K

/-- The honest running sum value `z_r = ⌊piece / 2^(K·r)⌋`. -/
def pieceZ (p : Fp) (r : ℕ) : Fp := ((p.val / 2 ^ (K * r) : ℕ) : Fp)

/-- Honest cell values of one double-and-add row, computed from the entering
accumulator `(x_a, y_a)` and the generator `(x_p, y_p)`
(`hash_to_point.rs::hash_piece` assignment formulas; total via `0⁻¹ = 0`). -/
def rowValue (acc : Fp × Fp) (gen : Fp × Fp) :
    Fp × Fp × (Fp × Fp) :=
  let lambda1 := (acc.2 - gen.2) * (acc.1 - gen.1)⁻¹
  let xR := lambda1 * lambda1 - acc.1 - gen.1
  let lambda2 := 2 * acc.2 * (acc.1 - xR)⁻¹ - lambda1
  let xANext := lambda2 * lambda2 - acc.1 - xR
  let yANext := lambda2 * (acc.1 - xANext) - acc.2
  (lambda1, lambda2, (xANext, yANext))

/-- The honest accumulator after `r` words of a piece. -/
def accAfter (G : Generators) (acc : Fp × Fp) (p : Fp) : ℕ → Fp × Fp
  | 0 => acc
  | r + 1 =>
    let prev := accAfter G acc p r
    (rowValue prev ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2

/-- Twice the exit `y`-coordinate, as derived by the following gate from the last row
of a piece and the next `x_A` cell: `2·y_B = 2·λ₂·(x_A - x_B) - Y_A`. -/
def nextYA {F : Type} [Add F] [Sub F] [Mul F] [OfNat F 2]
    (row : DoubleAndAddRow F) (xNext : F) : F :=
  2 * row.lambda2 * (row.xA - xNext) - DoubleAndAdd.yA row

namespace HashPiece

/-- Inputs of one piece: the piece value (an already-assigned cell), the entering
accumulator `x_A` (the cell written by the previous piece or initialization), and the
entering accumulator `y`-coordinate as a prover-side hint. -/
structure Input (F : Type) where
  piece : F
  xA : F
  yA : UnconstrainedDepNative field F
deriving CircuitType

/-- Outputs of one piece: its first and last gate rows (the composing circuit emits
the gates linking pieces), the exit `x_A` cell, and the exit accumulator
`y`-coordinate hint. -/
structure Output (n : ℕ) (F : Type) where
  first : DoubleAndAddRow F
  last : DoubleAndAddRow F
  xANext : F
  /-- The piece's running sum `[z_0, …, z_w]` (`z_0 = piece`; `z_{w+1} = 0` implicit).
  Halo2's `hash_piece` returns this whole vector (`hash_to_point.rs::hash_piece`); the
  composing circuits (`MerkleCRH`, `note_commit`, `commit_ivk`) read specific `z_r` cells
  for their decomposition / canonicity gates. -/
  zs : Vector F n
  yANext : UnconstrainedDepNative field F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ piece := default, xA := default, yA := fun _ => default }⟩

/-- `hash_piece` for `w + 1` words. -/
def main (G : Generators) (w : ℕ) (input : Var Input Fp) :
    Circuit Fp (Var (Output (w + 1)) Fp) := do
  -- running sum: z_0 is a copy of the piece, z_1 .. z_w are witnessed
  let z₀ <== input.piece
  let zRest ← witnessVector w (Vector.ofFn fun (i : Fin w) =>
    (input.piece.val / (2 ^ (K * (i.val + 1)) : ℕ)).toField)
  let zs : Vector (Expression Fp) (w + 1) :=
    Vector.cast (Nat.add_comm 1 w) ((#v[z₀] : Vector (Expression Fp) 1) ++ zRest)
  -- row cells: x_p, λ₁, λ₂ per word, and the next-row x_a per word.
  -- x_p is a pure generator-table read: the x-column of `G.S`, indexed by the piece
  -- word `z_r mod 2^K` (an IR table read, mirroring the fixed-base window tables)
  let genX : Vector Fp (2 ^ K) := Vector.ofFn fun k => (G.S k.val).x
  let xPs ← witnessVector (w + 1) (Vector.ofFn fun (i : Fin (w + 1)) =>
    genX[input.piece.val / (2 ^ (K * i.val) : ℕ) % (2 ^ K : ℕ)])
  -- λ₁, λ₂ and the next-row x_a stay native: their honest values chain through the
  -- recursive accumulator `accAfter` (row i needs i prior incomplete additions; the
  -- witness IR has no fold loops, and unrolling is O(i) term size per row), and they
  -- read the `UnconstrainedDepNative` hint `input.yA`, which no IR expression can
  -- consume
  let l1s ← witnessVectorNative (w + 1) fun env =>
    Vector.ofFn fun (i : Fin (w + 1)) =>
      (rowValue (accAfter G (env input.xA, input.yA env) (env input.piece) i.val)
        ((G.S (pieceWord (env input.piece) i.val)).x,
          (G.S (pieceWord (env input.piece) i.val)).y)).1
  let l2s ← witnessVectorNative (w + 1) fun env =>
    Vector.ofFn fun (i : Fin (w + 1)) =>
      (rowValue (accAfter G (env input.xA, input.yA env) (env input.piece) i.val)
        ((G.S (pieceWord (env input.piece) i.val)).x,
          (G.S (pieceWord (env input.piece) i.val)).y)).2.1
  let xAs ← witnessVectorNative (w + 1) fun env =>
    Vector.ofFn fun (i : Fin (w + 1)) =>
      (accAfter G (env input.xA, input.yA env) (env input.piece) (i.val + 1)).1
  -- the double-and-add row structs (x_a chained from the input cell)
  let dRows : Vector (Var DoubleAndAddRow Fp) (w + 1) := .ofFn fun i =>
    { xA := if _ : i.val = 0 then input.xA else xAs[i.val - 1]'(by omega),
      xP := xPs[i.val]'(i.isLt),
      lambda1 := l1s[i.val]'(i.isLt),
      lambda2 := l2s[i.val]'(i.isLt) }
  -- per-row generator lookups: the word is `z_r - 2^K·z_{r+1}` (with `z_{w+1} = 0`
  -- implicit on the last row), and `y_p` is derived from the row
  let lookupRows : Vector (Var GeneratorTableRow Fp) (w + 1) := .ofFn fun i =>
    let row := dRows[i.val]'(i.isLt)
    let word : Expression Fp :=
      if h : i.val = w then zs[i.val]'(by omega) else
        zs[i.val]'(by omega) - (2 ^ K : Fp) * zs[i.val + 1]'(by omega)
    { idx := word,
      x := row.xP,
      y := DoubleAndAdd.yA row * ((2 : Fp)⁻¹ : Fp) -
        row.lambda1 * (row.xA - row.xP) }
  Circuit.forEach lookupRows (lookup (generatorTable G))
  -- in-piece gates (`q_s2 = 1` rows): adjacent row pairs
  let gatePairs : Vector (Var Gate.Row Fp) w := .ofFn fun i =>
    { cur := dRows[i.val]'(by omega), next := dRows[i.val + 1]'(by omega) }
  Circuit.forEach gatePairs (Gate.circuit { qS2 := 1 })
  return {
    first := dRows[0]'(by omega),
    last := dRows[w]'(by omega),
    xANext := xAs[w]'(by omega),
    zs := zs,
    yANext := fun env =>
      (accAfter G (env input.xA, input.yA env) (env input.piece) (w + 1)).2 }

instance elaborated (G : Generators) (w : ℕ) :
    ElaboratedCircuit Fp Input (Output (w + 1)) (main G w) := by
  elaborate_circuit

private theorem two_ne_zero_Fp : (2 : Fp) ≠ 0 := by
  rw [show (2 : Fp) = ((2 : ℕ) : Fp) by norm_num, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD] at this

private theorem double_halved {f g s : Fp} (h : f * (2 : Fp)⁻¹ - g = s) :
    f - 2 * g = 2 * s := by
  have h2 := congrArg (fun t => 2 * t) h
  simp only [mul_sub] at h2
  rw [show (2 : Fp) * (f * (2 : Fp)⁻¹) = f from by
    rw [mul_comm f, ← mul_assoc, mul_inv_cancel₀ two_ne_zero_Fp, one_mul]] at h2
  linear_combination h2

/-- For one Sinsemilla step, the row equations determine the output coordinates. -/
theorem step_coordinates_of_constraints (S : ℕ → Point Fp) {A B : Point Fp} {m : ℕ}
    (hstep : Specs.Sinsemilla.step S m A = some B)
    {xp lambda1 lambda2 xa' YA' : Fp}
    (hYP : 2 * A.y - 2 * lambda1 * (A.x - xp) = 2 * (S m).y)
    (hXP : xp = (S m).x)
    (hYA : 2 * A.y = (lambda1 + lambda2) * (A.x - (lambda1 * lambda1 - A.x - xp)))
    (hSecant : lambda2 * lambda2 = xa' + (lambda1 * lambda1 - A.x - xp) + A.x)
    (hYCheck : 4 * lambda2 * (A.x - xa') = 4 * A.y + 2 * YA') :
    xa' = B.x ∧ YA' = 2 * B.y := by
  exact DoubleAndAdd.coordinates_of_constraints (S := S m)
    (by simpa [Specs.Sinsemilla.step] using hstep)
    hYP hXP hYA hSecant hYCheck

/--
The honest-prover counterpart of `step_coordinates_of_constraints`: when the spec-level step
`(A ⸭ S(m)) ⸭ A = B` is defined, the honest cell values (the `rowValue` assignment
formulas, given as hypotheses) satisfy the row's lookup-`y` derivation and `Y_A`
invariant, and the next accumulator is `B`.
-/
theorem step_honest (S : ℕ → Point Fp) {A B : Point Fp} {m : ℕ}
    (hstep : Specs.Sinsemilla.step S m A = some B)
    {l1 l2 xa' ya' : Fp}
    (hl1 : l1 = (A.y - (S m).y) * (A.x - (S m).x)⁻¹)
    (hl2 : l2 = 2 * A.y * (A.x - (l1 * l1 - A.x - (S m).x))⁻¹ - l1)
    (hxa : xa' = l2 * l2 - A.x - (l1 * l1 - A.x - (S m).x))
    (hya : ya' = l2 * (A.x - xa') - A.y) :
    A.y - l1 * (A.x - (S m).x) = (S m).y ∧
    2 * A.y = (l1 + l2) * (A.x - (l1 * l1 - A.x - (S m).x)) ∧
    xa' = B.x ∧ ya' = B.y := by
  -- unfold the spec-level step into its two incomplete additions (as in `step_coordinates_of_constraints`)
  unfold Specs.Sinsemilla.step Point.doubleAndAdd at hstep
  by_cases hc₁ : A = 0 ∨ S m = 0 ∨ A.x = (S m).x
  · rw [Point.incompleteAdd_def, if_pos hc₁] at hstep
    simp at hstep
  rw [Point.incompleteAdd_def, if_neg hc₁] at hstep
  push Not at hc₁
  obtain ⟨hA0, hS0, hAxS⟩ := hc₁
  set R : Point Fp := A + S m with hR_def
  change Point.incompleteAdd R A = some B at hstep
  by_cases hc₂ : R = 0 ∨ A = 0 ∨ R.x = A.x
  · rw [Point.incompleteAdd_def, if_pos hc₂] at hstep
    simp at hstep
  rw [Point.incompleteAdd_def, if_neg hc₂] at hstep
  push Not at hc₂
  obtain ⟨hR0, -, hRxA⟩ := hc₂
  have hB : B = R + A := by
    have := Option.some.inj hstep
    rw [← this]
  have point_ne_zero : ∀ {P : Point Fp}, P ≠ 0 →
      ({ x := P.x, y := P.y } : Point Fp) ≠ Point.zero := by
    intro P hP h
    apply hP
    simpa [Point.zero_def] using h
  -- the first addition: `R = A ⸭ S(m)`, with the chord through `A` and `S(m)`
  have hRadd := Point.nondegenerateAdd_eq_add
    (p := { x := A.x, y := A.y }) (q := { x := (S m).x, y := (S m).y })
    (point_ne_zero hA0) (point_ne_zero hS0) hAxS
  rw [← hR_def] at hRadd
  have hRx := congrArg Point.x hRadd
  have hRy := congrArg Point.y hRadd
  simp only [Point.nondegenerateAdd] at hRx hRy
  set slope₁ : Fp := ((S m).y - A.y) * ((S m).x - A.x)⁻¹ with hslope₁
  have hAxS' : A.x - (S m).x ≠ 0 := sub_ne_zero.mpr hAxS
  -- the honest `λ₁` is the first chord slope, and the `y_p` derivation recovers `S(m)`
  have hl1' : l1 = slope₁ := by
    rw [hl1, hslope₁, show A.x - (S m).x = -((S m).x - A.x) by ring, inv_neg]
    ring
  have hyp : A.y - l1 * (A.x - (S m).x) = (S m).y := by
    rw [hl1, mul_assoc, inv_mul_cancel₀ hAxS', mul_one]
    ring
  have hxR : l1 * l1 - A.x - (S m).x = R.x := by
    rw [hl1']
    exact hRx
  have hyR : l1 * (A.x - R.x) - A.y = R.y := by
    rw [hl1', ← hRx]
    exact hRy
  have hRxA' : A.x - R.x ≠ 0 := sub_ne_zero.mpr fun h => hRxA h.symm
  -- the honest `λ₂` satisfies the `Y_A` invariant and is the second chord slope
  have hYA : 2 * A.y = (l1 + l2) * (A.x - (l1 * l1 - A.x - (S m).x)) := by
    rw [hxR, hl2, hxR]
    have hc := mul_inv_cancel₀ hRxA'
    linear_combination (-(2 * A.y)) * hc
  -- the second addition: `B = A ⸭ R`, with the chord through `A` and `R`
  have hBadd := Point.nondegenerateAdd_eq_add
    (p := { x := R.x, y := R.y }) (q := { x := A.x, y := A.y })
    (point_ne_zero hR0) (point_ne_zero hA0) hRxA
  rw [← hB] at hBadd
  have hBx := congrArg Point.x hBadd
  have hBy := congrArg Point.y hBadd
  simp only [Point.nondegenerateAdd] at hBx hBy
  set slope₂ : Fp := (R.y - A.y) * (R.x - A.x)⁻¹ with hslope₂
  have hslope₂_alt : (A.y - R.y) * (A.x - R.x)⁻¹ = slope₂ := by
    rw [hslope₂, show A.y - R.y = -(R.y - A.y) by ring,
      show A.x - R.x = -(R.x - A.x) by ring, inv_neg]
    ring
  rw [hslope₂_alt] at hBx hBy
  have hl2' : l2 = slope₂ := by
    apply mul_right_cancel₀ hRxA'
    rw [hslope₂, mul_assoc,
      show (R.x - A.x)⁻¹ * (A.x - R.x) = -1 from by
        rw [show A.x - R.x = -(R.x - A.x) by ring, mul_neg,
          inv_mul_cancel₀ (sub_ne_zero.mpr hRxA)],
      mul_neg_one]
    have hYA' : 2 * A.y = (l1 + l2) * (A.x - R.x) := by
      rw [← hxR]
      exact hYA
    linear_combination -hYA' - hyR
  have hline₂ : l2 * (A.x - R.x) = A.y - R.y := by
    have hYA' : 2 * A.y = (l1 + l2) * (A.x - R.x) := by
      rw [← hxR]
      exact hYA
    linear_combination -hYA' - hyR
  -- the honest next accumulator is `B`
  have hBx' : xa' = B.x := by
    rw [← hBx, hxa, hl2', hxR]
    ring
  have hBy' : ya' = B.y := by
    rw [hl2'] at hline₂
    rw [hya, hBx', ← hBy, hl2', hBx]
    linear_combination hline₂
  exact ⟨hyp, hYA, hBx', hBy'⟩

/-- The honest accumulator chain follows the spec-level chain points, as long as the
spec-level chain is defined. -/
theorem accAfter_eq_chain (G : Generators) {A : Point Fp} (p : Fp)
    {r : ℕ} {Ar : Point Fp}
    (hchain : Specs.Sinsemilla.hashToPoint G.S A
      ((List.range r).map (pieceWord p)) = some Ar) :
    accAfter G (A.x, A.y) p r = (Ar.x, Ar.y) := by
  induction r generalizing Ar with
  | zero =>
    rw [show ((List.range 0).map (pieceWord p)) = ([] : List ℕ) from rfl,
      Specs.Sinsemilla.hashToPoint_nil] at hchain
    obtain rfl : A = Ar := Option.some.inj hchain
    rfl
  | succ r ih =>
    rw [List.range_succ] at hchain
    simp only [List.map_append, List.map_cons, List.map_nil] at hchain
    rw [Specs.Sinsemilla.hashToPoint_concat] at hchain
    cases hpre : Specs.Sinsemilla.hashToPoint G.S A
        ((List.range r).map (pieceWord p)) with
    | none =>
      rw [hpre] at hchain
      simp at hchain
    | some Ap =>
      rw [hpre] at hchain
      replace hchain : Specs.Sinsemilla.step G.S (pieceWord p r) Ap = some Ar :=
        hchain
      have hacc := ih hpre
      show (rowValue (accAfter G (A.x, A.y) p r)
        ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2 = (Ar.x, Ar.y)
      rw [hacc]
      have hh := step_honest G.S hchain
        (l1 := (rowValue (Ap.x, Ap.y)
          ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1)
        (l2 := (rowValue (Ap.x, Ap.y)
          ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.1)
        (xa' := (rowValue (Ap.x, Ap.y)
          ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2.1)
        (ya' := (rowValue (Ap.x, Ap.y)
          ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2.2)
        rfl rfl rfl rfl
      exact Prod.ext hh.2.2.1 hh.2.2.2

/-! ### Honest running-sum values -/

theorem pieceWord_lt (p : Fp) (r : ℕ) : pieceWord p r < 2 ^ K :=
  Nat.mod_lt _ (by norm_num [K])

/-- The evaluated generator-column read is the honest `x_p` value: the range guard of
the `.listGet` table read discharges since the word is a `mod 2^K` residue, and the raw
div/mod index folds back into `pieceWord` (with `FiniteField.val = ZMod.val`)
definitionally. The LHS is the `circuit_norm` normal form of the witness-IR
completeness hypothesis for `xPs`. -/
private theorem genX_read_value (G : Generators) (p : Fp) (r : ℕ) :
    (if _ : FiniteField.val p / 2 ^ (K * r) % 2 ^ K < 2 ^ K
      then (G.S (FiniteField.val p / 2 ^ (K * r) % 2 ^ K)).x else 0)
    = (G.S (pieceWord p r)).x := by
  have hlt : FiniteField.val p / 2 ^ (K * r) % 2 ^ K < 2 ^ K :=
    Nat.mod_lt _ (by norm_num [K])
  simp only [dif_pos hlt]
  rfl

theorem pieceZ_zero (p : Fp) : pieceZ p 0 = p := by
  unfold pieceZ
  rw [Nat.mul_zero, pow_zero, Nat.div_one]
  exact ZMod.natCast_rightInverse p

theorem pieceZ_succ (p : Fp) (r : ℕ) :
    pieceZ p r = (pieceWord p r : Fp) + 2 ^ K * pieceZ p (r + 1) := by
  unfold pieceZ pieceWord
  rw [show K * (r + 1) = K * r + K by ring, pow_add, ← Nat.div_div_eq_div_mul]
  generalize p.val / 2 ^ (K * r) = n
  conv_lhs => rw [← Nat.mod_add_div n (2 ^ K)]
  push_cast
  ring

theorem pieceZ_last {p : Fp} {w : ℕ} (hp : p.val < 2 ^ (K * (w + 1))) :
    pieceZ p w = (pieceWord p w : Fp) := by
  unfold pieceZ pieceWord
  rw [Nat.mod_eq_of_lt]
  apply Nat.div_lt_of_lt_mul
  rw [← pow_add, show K * w + K = K * (w + 1) by ring]
  exact hp

/-- Telescoped base-`2^K` running sum (mirrors the short-mul chain lemma). -/
theorem chain_eq_sum {n : ℕ} (z : ℕ → Fp) (ms : ℕ → ℕ)
    (hword : ∀ r < n, z r = (ms r : Fp) + 2 ^ K * z (r + 1))
    (hzn : z n = 0) :
    z 0 = ((∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) : Fp) := by
  have key : ∀ r ≤ n,
      z 0 = ((∑ j ∈ Finset.range r, ms j * 2 ^ (K * j) : ℕ) : Fp)
        + z r * ((2 ^ (K * r) : ℕ) : Fp) := by
    intro r hr
    induction r with
    | zero => simp
    | succ v ih =>
      rw [ih (by omega), hword v (by omega), Finset.sum_range_succ]
      push_cast
      rw [show K * (v + 1) = K * v + K by ring]
      push_cast [pow_add]
      ring
  have hn := key n (by omega)
  rw [hzn, zero_mul, _root_.add_zero] at hn
  exact hn

/-- A piece that fits in `K·m` bits is the base-`2^K` recombination of its `K`-bit words. -/
theorem piece_recombine (p : Fp) (m : ℕ) (hp : p.val < 2 ^ (K * m)) :
    p = ((∑ r ∈ Finset.range m, pieceWord p r * 2 ^ (K * r) : ℕ) : Fp) := by
  have hzn : pieceZ p m = 0 := by simp only [pieceZ, Nat.div_eq_of_lt hp, Nat.cast_zero]
  have h := chain_eq_sum (n := m) (pieceZ p) (pieceWord p) (fun r _ => pieceZ_succ p r) hzn
  rwa [pieceZ_zero] at h

/-- Each running sum `z_r` is the recombination of the words from position `r` onward
(the suffix sum). Mirrors `chain_eq_sum` but characterizes every prefix exit, not just
`z_0`. -/
private theorem chain_eq_suffix_sum {w : ℕ} (zV : ℕ → Fp) (ms : ℕ → ℕ)
    (hword : ∀ s, s < w → zV s = (ms s : Fp) + 2 ^ K * zV (s + 1))
    (hlast : zV w = (ms w : Fp)) (d r : ℕ) (hrw : r + d = w) :
    zV r = ((∑ j ∈ Finset.range (d + 1), ms (r + j) * 2 ^ (K * j) : ℕ) : Fp) := by
  have h := chain_eq_sum (fun j => if j ≤ d then zV (r + j) else 0) (fun j => ms (r + j))
    (n := d + 1)
    (by
      intro s hs
      dsimp only
      rw [if_pos (show s ≤ d by omega)]
      rcases Nat.lt_or_ge s d with hsd | hsd
      · rw [if_pos (show s + 1 ≤ d by omega), show r + (s + 1) = r + s + 1 by omega]
        exact hword (r + s) (by omega)
      · obtain rfl : s = d := by omega
        rw [if_neg (show ¬ s + 1 ≤ s by omega), mul_zero, _root_.add_zero,
          show r + s = w by omega]
        exact hlast)
    (by dsimp only; rw [if_neg (show ¬ d + 1 ≤ d by omega)])
  simpa using h

/-- The verifier-side contract of one piece, see `step_coordinates_of_constraints` for the chain step. The
chain runs through the first `w` words; the last word's lookup facts are exposed so the
composing circuit can finish the step with its boundary gate. -/
def Spec (G : Generators) (w : ℕ) (input : Value Input Fp)
    (output : Value (Output (w + 1)) Fp) (_ : ProverData Fp) : Prop :=
  ∃ ms : ℕ → ℕ,
    (∀ r, ms r < 2 ^ K) ∧
    input.piece = ((∑ r ∈ Finset.range (w + 1), ms r * 2 ^ (K * r) : ℕ) : Fp) ∧
    output.zs = Vector.ofFn (fun r : Fin (w + 1) =>
      ((∑ j ∈ Finset.range (w + 1 - r.val), ms (r.val + j) * 2 ^ (K * j) : ℕ) : Fp)) ∧
    output.first.xA = input.xA ∧
    output.last.xP = (G.S (ms w)).x ∧
    DoubleAndAdd.yA output.last * (2 : Fp)⁻¹
        - output.last.lambda1 * (output.last.xA - output.last.xP) = (G.S (ms w)).y ∧
    ∀ A : Point Fp, A.OnCurve → A.x = input.xA →
      2 * A.y = DoubleAndAdd.yA output.first →
      ∀ B, Specs.Sinsemilla.hashToPoint G.S A
          ((List.range w).map ms) = some B →
        output.last.xA = B.x ∧ 2 * B.y = DoubleAndAdd.yA output.last

/--
The honest-prover contract of one piece. The entering accumulator hint must be a
genuine non-identity curve point matching the `x_A` cell, the piece value must fit in
`K·(w+1)` bits, and the spec-level chain over the piece's chunks must be defined
(non-exceptional).
-/
def ProverAssumptions (G : Generators) (w : ℕ) (input : ProverValue Input Fp)
    (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  (show Fp from input.piece).val < 2 ^ (K * (w + 1)) ∧
  ∃ (A B : Point Fp), A.OnCurve ∧ A.x = input.xA ∧ A.y = input.yA ∧
    Specs.Sinsemilla.hashToPoint G.S A
      ((List.range (w + 1)).map (pieceWord input.piece)) = some B

/--
What the honest prover guarantees to the composing circuit: the first row starts at the
input accumulator with the `Y_A` invariant, the exit cell satisfies the secant equation
of the following (boundary) gate by construction, and the exit accumulator is the
spec-level chain point with its boundary-gate `Y_A` derivation.
-/
def ProverSpec (G : Generators) (w : ℕ) (input : ProverValue Input Fp)
    (output : ProverValue (Output (w + 1)) Fp) (_ : ProverHint Fp) : Prop :=
  output.first.xA = input.xA ∧
  output.xANext = output.last.lambda2 * output.last.lambda2
    - output.last.xA - DoubleAndAdd.xR output.last ∧
  output.zs = Vector.ofFn (fun r : Fin (w + 1) => pieceZ input.piece r.val) ∧
  ∀ A : Point Fp, A ≠ 0 → A.x = input.xA → A.y = input.yA →
    DoubleAndAdd.yA output.first = 2 * A.y ∧
    ∀ B, Specs.Sinsemilla.hashToPoint G.S A
        ((List.range (w + 1)).map (pieceWord input.piece)) = some B →
      output.xANext = B.x ∧ output.yANext = B.y ∧
      nextYA output.last output.xANext = 2 * B.y

private theorem range_prefix_some (S : ℕ → Point Fp)
    (Q : Point Fp) (f : ℕ → ℕ) {n : ℕ} {B : Point Fp}
    (hn : Specs.Sinsemilla.hashToPoint S Q ((List.range n).map f) = some B)
    {r : ℕ} (hr : r ≤ n) :
    ∃ C, Specs.Sinsemilla.hashToPoint S Q ((List.range r).map f) = some C := by
  obtain ⟨k, rfl⟩ : ∃ k, n = r + k := ⟨n - r, by omega⟩
  rw [List.range_add, List.map_append,
    Specs.Sinsemilla.hashToPoint_append] at hn
  cases hc : Specs.Sinsemilla.hashToPoint S Q ((List.range r).map f) with
  | none =>
    rw [hc] at hn
    simp at hn
  | some C =>
    exact ⟨C, rfl⟩

/--
The chain facts of one honest piece: at every row the derived `Y_A` expression is twice
the honest accumulator `y` and the `y_p` derivation lands on the generator, and the
piece exits at the spec-level chain point. Splitting this from `completeness` keeps
each declaration within the elaboration budget.
-/
private theorem completeness_aux (G : Generators) (w : ℕ) (p xA yA : Fp)
    {A B : Point Fp} (hAx : A.x = xA) (hAy : A.y = yA)
    (hchain : Specs.Sinsemilla.hashToPoint G.S A
      ((List.range (w + 1)).map (pieceWord p)) = some B) :
    (∀ r, r ≤ w →
      ((rowValue (accAfter G (xA, yA) p r)
            ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1
          + (rowValue (accAfter G (xA, yA) p r)
            ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.1)
        * ((accAfter G (xA, yA) p r).1
          - ((rowValue (accAfter G (xA, yA) p r)
                ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1
              * (rowValue (accAfter G (xA, yA) p r)
                ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1
            - (accAfter G (xA, yA) p r).1 - (G.S (pieceWord p r)).x))
        = 2 * (accAfter G (xA, yA) p r).2 ∧
      (accAfter G (xA, yA) p r).2
          - (rowValue (accAfter G (xA, yA) p r)
              ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1
            * ((accAfter G (xA, yA) p r).1 - (G.S (pieceWord p r)).x)
        = (G.S (pieceWord p r)).y) ∧
    accAfter G (xA, yA) p (w + 1) = (B.x, B.y) := by
  subst hAx hAy
  refine ⟨?_, accAfter_eq_chain G p hchain⟩
  intro r hr
  obtain ⟨Ar, hAr⟩ := range_prefix_some _ _ _ hchain (show r ≤ w + 1 by omega)
  obtain ⟨Ar1, hAr1⟩ := range_prefix_some _ _ _ hchain (show r + 1 ≤ w + 1 by omega)
  have hstep : Specs.Sinsemilla.step G.S (pieceWord p r) Ar = some Ar1 := by
    rw [List.range_succ] at hAr1
    simp only [List.map_append, List.map_cons, List.map_nil] at hAr1
    rw [Specs.Sinsemilla.hashToPoint_concat, hAr] at hAr1
    exact hAr1
  have hacc := accAfter_eq_chain G p hAr
  have hh := step_honest G.S hstep
    (l1 := (rowValue (Ar.x, Ar.y)
      ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1)
    (l2 := (rowValue (Ar.x, Ar.y)
      ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.1)
    (xa' := (rowValue (Ar.x, Ar.y)
      ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2.1)
    (ya' := (rowValue (Ar.x, Ar.y)
      ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2.2)
    rfl rfl rfl rfl
  rw [hacc]
  exact ⟨hh.2.1.symm, hh.1⟩

theorem completeness (G : Generators) (w : ℕ) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G w)
      (ProverAssumptions G w) (ProverSpec G w) := by
  circuit_proof_start [Gate.circuit, Gate.Spec,
    generatorTable]
  obtain ⟨hbound, A, B, hAon, hAx, hAy, hB⟩ := h_assumptions
  have hA0 : A ≠ 0 := Point.ne_zero_of_onCurve hAon
  obtain ⟨h_z0, h_zs, h_xPs, h_l1s, h_l2s, h_xAs, -⟩ := h_env
  replace h_zs : ∀ i : Fin w, env.get (i₀ + 1 + i.val) = pieceZ input_piece (i.val + 1) := by
    intro i
    simp only [h_zs i, pieceZ]
    rfl
  replace h_xPs : ∀ i : Fin (w + 1), env.get (i₀ + 1 + w + i.val)
      = (G.S (pieceWord input_piece i.val)).x :=
    fun i => (h_xPs i).trans (genX_read_value G input_piece i.val)
  have haux := completeness_aux G w input_piece input_xA input_yA hAx hAy hB
  simp only [Vector.getElem_append,
    Vector.getElem_mapRange, circuit_norm]
  -- cell-value views
  have hxA_cell : ∀ r : ℕ, r < w + 1 →
      Expression.eval env.toEnvironment
        (if _ : r = 0 then input_var.xA
          else var { index := i₀ + 1 + w + (w + 1) + (w + 1) + (w + 1) + (r - 1) })
        = (accAfter G (input_xA, input_yA) input_piece r).1 := by
    intro r hr
    by_cases hr0 : r = 0
    · rw [dif_pos hr0, hr0]
      exact h_input.2.1
    · rw [dif_neg hr0]
      have h : env.get (i₀ + 1 + w + (w + 1) + (w + 1) + (w + 1) + (r - 1))
          = (accAfter G (input_xA, input_yA) input_piece (r - 1 + 1)).1 :=
        h_xAs ⟨r - 1, by omega⟩
      rw [show r - 1 + 1 = r from by omega] at h
      simp only [circuit_norm]
      exact h
  have hxA_last : Expression.eval env.toEnvironment
      (if w = 0 then input_var.xA
        else var { index := i₀ + 1 + w + (w + 1) + (w + 1) + (w + 1) + (w - 1) })
      = (accAfter G (input_xA, input_yA) input_piece w).1 := by
    by_cases hw0 : w = 0
    · rw [if_pos hw0, hw0]
      exact h_input.2.1
    · rw [if_neg hw0]
      have h : env.get (i₀ + 1 + w + (w + 1) + (w + 1) + (w + 1) + (w - 1))
          = (accAfter G (input_xA, input_yA) input_piece (w - 1 + 1)).1 :=
        h_xAs ⟨w - 1, by omega⟩
      rw [show w - 1 + 1 = w from by omega] at h
      simp only [circuit_norm]
      exact h
  -- definitional accumulator recurrences (cheap at symbolic index)
  have haccx : ∀ r : ℕ, (accAfter G (input_xA, input_yA) input_piece (r + 1)).1
      = (rowValue (accAfter G (input_xA, input_yA) input_piece r)
            ((G.S (pieceWord input_piece r)).x, (G.S (pieceWord input_piece r)).y)).2.1
          * (rowValue (accAfter G (input_xA, input_yA) input_piece r)
            ((G.S (pieceWord input_piece r)).x, (G.S (pieceWord input_piece r)).y)).2.1
        - (accAfter G (input_xA, input_yA) input_piece r).1
        - ((rowValue (accAfter G (input_xA, input_yA) input_piece r)
              ((G.S (pieceWord input_piece r)).x, (G.S (pieceWord input_piece r)).y)).1
            * (rowValue (accAfter G (input_xA, input_yA) input_piece r)
              ((G.S (pieceWord input_piece r)).x, (G.S (pieceWord input_piece r)).y)).1
          - (accAfter G (input_xA, input_yA) input_piece r).1
          - (G.S (pieceWord input_piece r)).x) :=
    fun _ => rfl
  have haccy : ∀ r : ℕ, (accAfter G (input_xA, input_yA) input_piece (r + 1)).2
      = (rowValue (accAfter G (input_xA, input_yA) input_piece r)
            ((G.S (pieceWord input_piece r)).x, (G.S (pieceWord input_piece r)).y)).2.1
          * ((accAfter G (input_xA, input_yA) input_piece r).1
            - (accAfter G (input_xA, input_yA) input_piece (r + 1)).1)
        - (accAfter G (input_xA, input_yA) input_piece r).2 :=
    fun _ => rfl
  have h2 := mul_inv_cancel₀ two_ne_zero_Fp
  refine ⟨⟨h_z0, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- lookups
    intro i
    refine ⟨pieceWord input_piece ↑i, pieceWord_lt _ _, ?_, h_xPs i, ?_⟩
    · -- the running-sum word equation
      split_ifs <;> try omega
      · -- ↑i = w, ↑i < 1: single-word piece
        rw [show w = 0 from by omega] at hbound
        simp only [List.getElem_singleton, circuit_norm]
        rw [h_z0, show pieceWord input_piece ↑i = pieceWord input_piece 0 from by
            rw [show (↑i : ℕ) = 0 from by omega],
          ← pieceZ_last hbound]
        exact (pieceZ_zero input_piece).symm
      · -- ↑i = w ≥ 1: last word
        simp only [circuit_norm]
        have hzv : env.get (i₀ + 1 + ((↑i : ℕ) - 1))
            = pieceZ input_piece ((↑i : ℕ) - 1 + 1) := h_zs ⟨↑i - 1, by omega⟩
        rw [show (↑i : ℕ) - 1 + 1 = ↑i from by omega] at hzv
        rw [hzv, show (↑i : ℕ) = w from by omega]
        exact pieceZ_last hbound
      · -- ↑i = 0 < w
        simp only [List.getElem_singleton, circuit_norm,
          show ∀ a : ℕ, a + 1 - 1 = a from fun _ => rfl]
        rw [show (↑i : ℕ) = 0 from by omega]
        have hz1 : env.get (i₀ + 1 + 0) = pieceZ input_piece (0 + 1) := h_zs ⟨0, by omega⟩
        rw [h_z0, hz1]
        linear_combination pieceZ_succ input_piece 0 - pieceZ_zero input_piece
      · -- 1 ≤ ↑i < w
        simp only [circuit_norm, show ∀ a : ℕ, a + 1 - 1 = a from fun _ => rfl]
        have hzv : env.get (i₀ + 1 + ((↑i : ℕ) - 1))
            = pieceZ input_piece ((↑i : ℕ) - 1 + 1) := h_zs ⟨↑i - 1, by omega⟩
        rw [show (↑i : ℕ) - 1 + 1 = ↑i from by omega] at hzv
        have hz1 : env.get (i₀ + 1 + (↑i : ℕ)) = pieceZ input_piece ((↑i : ℕ) + 1) :=
          h_zs ⟨↑i, by omega⟩
        rw [hzv, hz1]
        linear_combination pieceZ_succ input_piece ↑i
    · -- the `y_p` lookup derivation
      have hp : env.get (i₀ + 1 + w + (↑i : ℕ))
          = (G.S (pieceWord input_piece ↑i)).x := h_xPs i
      have hl1 : env.get (i₀ + 1 + w + (w + 1) + (↑i : ℕ))
          = (rowValue (accAfter G (input_xA, input_yA) input_piece ↑i)
              ((G.S (pieceWord input_piece ↑i)).x,
                (G.S (pieceWord input_piece ↑i)).y)).1 := h_l1s i
      have hl2 : env.get (i₀ + 1 + w + (w + 1) + (w + 1) + (↑i : ℕ))
          = (rowValue (accAfter G (input_xA, input_yA) input_piece ↑i)
              ((G.S (pieceWord input_piece ↑i)).x,
                (G.S (pieceWord input_piece ↑i)).y)).2.1 := h_l2s i
      simp only [DoubleAndAdd.yA, DoubleAndAdd.xR, circuit_norm]
      rw [hxA_cell ↑i (by omega), hp, hl1, hl2]
      obtain ⟨hYI, hYp⟩ := haux.1 ↑i (by omega)
      linear_combination (2 : Fp)⁻¹ * hYI + hYp
        + (accAfter G (input_xA, input_yA) input_piece ↑i).2 * h2
  · -- in-piece gates
    intro i
    have hp1 : env.get (i₀ + 1 + w + (↑i : ℕ))
        = (G.S (pieceWord input_piece ↑i)).x := h_xPs ⟨↑i, by omega⟩
    have hl11 : env.get (i₀ + 1 + w + (w + 1) + (↑i : ℕ))
        = (rowValue (accAfter G (input_xA, input_yA) input_piece ↑i)
            ((G.S (pieceWord input_piece ↑i)).x,
              (G.S (pieceWord input_piece ↑i)).y)).1 := h_l1s ⟨↑i, by omega⟩
    have hl21 : env.get (i₀ + 1 + w + (w + 1) + (w + 1) + (↑i : ℕ))
        = (rowValue (accAfter G (input_xA, input_yA) input_piece ↑i)
            ((G.S (pieceWord input_piece ↑i)).x,
              (G.S (pieceWord input_piece ↑i)).y)).2.1 := h_l2s ⟨↑i, by omega⟩
    have hp2 : env.get (i₀ + 1 + w + ((↑i : ℕ) + 1))
        = (G.S (pieceWord input_piece ((↑i : ℕ) + 1))).x := h_xPs ⟨↑i + 1, by omega⟩
    have hl12 : env.get (i₀ + 1 + w + (w + 1) + ((↑i : ℕ) + 1))
        = (rowValue (accAfter G (input_xA, input_yA) input_piece ((↑i : ℕ) + 1))
            ((G.S (pieceWord input_piece ((↑i : ℕ) + 1))).x,
              (G.S (pieceWord input_piece ((↑i : ℕ) + 1))).y)).1 := h_l1s ⟨↑i + 1, by omega⟩
    have hl22 : env.get (i₀ + 1 + w + (w + 1) + (w + 1) + ((↑i : ℕ) + 1))
        = (rowValue (accAfter G (input_xA, input_yA) input_piece ((↑i : ℕ) + 1))
            ((G.S (pieceWord input_piece ((↑i : ℕ) + 1))).x,
              (G.S (pieceWord input_piece ((↑i : ℕ) + 1))).y)).2.1 := h_l2s ⟨↑i + 1, by omega⟩
    obtain ⟨hYI1, -⟩ := haux.1 ↑i (by omega)
    obtain ⟨hYI2, -⟩ := haux.1 (↑i + 1) (by omega)
    constructor
    · -- secant across rows `↑i`, `↑i + 1`
      simp only [DoubleAndAdd.xR]
      rw [hxA_cell ↑i (by omega), hxA_cell (↑i + 1) (by omega), hp1, hl11, hl21]
      linear_combination -(haccx ↑i)
    · -- the `Y_A` check across rows `↑i`, `↑i + 1`
      simp only [Gate.yLhs, Gate.yRhs, Gate.qS3, DoubleAndAdd.yA, DoubleAndAdd.xR]
      rw [hxA_cell ↑i (by omega), hxA_cell (↑i + 1) (by omega),
        hp1, hl11, hl21, hp2, hl12, hl22]
      linear_combination -2 * hYI1 - 2 * hYI2 - 4 * haccy ↑i
  · -- the exit cell satisfies the boundary secant by construction
    have hxw : env.get (i₀ + 1 + w + (w + 1) + (w + 1) + (w + 1) + w)
        = (accAfter G (input_xA, input_yA) input_piece (w + 1)).1 := h_xAs ⟨w, by omega⟩
    have hpw : env.get (i₀ + 1 + w + w)
        = (G.S (pieceWord input_piece w)).x := h_xPs ⟨w, by omega⟩
    have hl1w : env.get (i₀ + 1 + w + (w + 1) + w)
        = (rowValue (accAfter G (input_xA, input_yA) input_piece w)
            ((G.S (pieceWord input_piece w)).x,
              (G.S (pieceWord input_piece w)).y)).1 := h_l1s ⟨w, by omega⟩
    have hl2w : env.get (i₀ + 1 + w + (w + 1) + (w + 1) + w)
        = (rowValue (accAfter G (input_xA, input_yA) input_piece w)
            ((G.S (pieceWord input_piece w)).x,
              (G.S (pieceWord input_piece w)).y)).2.1 := h_l2s ⟨w, by omega⟩
    simp only [DoubleAndAdd.xR]
    rw [hxw, hxA_last, hpw, hl1w, hl2w]
    linear_combination haccx w
  · -- the running-sum vector
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_map, Vector.getElem_ofFn]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [Vector.getElem_cast, Vector.getElem_append, circuit_norm, pieceZ_zero]
      exact h_z0
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      simp only [Vector.getElem_cast, Vector.getElem_append, circuit_norm, Vector.getElem_mapRange]
      exact h_zs ⟨k, by omega⟩
  · -- the chain contract
    intro A' hA'0 hA'x hA'y
    obtain rfl : A' = A := by
      rcases A with ⟨Ax, Ay⟩
      rcases A' with ⟨Ax', Ay'⟩
      simp only [Point.mk.injEq]
      exact ⟨hA'x.trans hAx.symm, hA'y.trans hAy.symm⟩
    constructor
    · -- entering `Y_A` invariant
      have hp0 : env.get (i₀ + 1 + w)
          = (G.S (pieceWord input_piece 0)).x := h_xPs ⟨0, by omega⟩
      have hl10 : env.get (i₀ + 1 + w + (w + 1))
          = (rowValue (accAfter G (input_xA, input_yA) input_piece 0)
              ((G.S (pieceWord input_piece 0)).x,
                (G.S (pieceWord input_piece 0)).y)).1 := h_l1s ⟨0, by omega⟩
      have hl20 : env.get (i₀ + 1 + w + (w + 1) + (w + 1))
          = (rowValue (accAfter G (input_xA, input_yA) input_piece 0)
              ((G.S (pieceWord input_piece 0)).x,
                (G.S (pieceWord input_piece 0)).y)).2.1 := h_l2s ⟨0, by omega⟩
      obtain ⟨hYI0, -⟩ := haux.1 0 (by omega)
      simp only [DoubleAndAdd.yA, DoubleAndAdd.xR]
      rw [hp0, hl10, hl20]
      have hacc0x : (accAfter G (input_xA, input_yA) input_piece 0).1 = input_xA := rfl
      have hacc0y : (accAfter G (input_xA, input_yA) input_piece 0).2 = input_yA := rfl
      linear_combination hYI0
        - 2 * ((rowValue (accAfter G (input_xA, input_yA) input_piece 0)
              ((G.S (pieceWord input_piece 0)).x, (G.S (pieceWord input_piece 0)).y)).1
            + (rowValue (accAfter G (input_xA, input_yA) input_piece 0)
              ((G.S (pieceWord input_piece 0)).x,
                (G.S (pieceWord input_piece 0)).y)).2.1) * hacc0x
        + 2 * hacc0y - 2 * hAy
    · -- exit accumulator
      intro B2 hB2
      rw [hB] at hB2
      rw [← Option.some.inj hB2]
      have hxw : env.get (i₀ + 1 + w + (w + 1) + (w + 1) + (w + 1) + w)
          = (accAfter G (input_xA, input_yA) input_piece (w + 1)).1 := h_xAs ⟨w, by omega⟩
      have hexity : (accAfter G (input_xA, input_yA) input_piece (w + 1)).2 = B.y := by
        rw [haux.2]
      refine ⟨by rw [hxw, haux.2], hexity, ?_⟩
      have hpw : env.get (i₀ + 1 + w + w)
          = (G.S (pieceWord input_piece w)).x := h_xPs ⟨w, by omega⟩
      have hl1w : env.get (i₀ + 1 + w + (w + 1) + w)
          = (rowValue (accAfter G (input_xA, input_yA) input_piece w)
              ((G.S (pieceWord input_piece w)).x,
                (G.S (pieceWord input_piece w)).y)).1 := h_l1s ⟨w, by omega⟩
      have hl2w : env.get (i₀ + 1 + w + (w + 1) + (w + 1) + w)
          = (rowValue (accAfter G (input_xA, input_yA) input_piece w)
              ((G.S (pieceWord input_piece w)).x,
                (G.S (pieceWord input_piece w)).y)).2.1 := h_l2s ⟨w, by omega⟩
      obtain ⟨hYIw, -⟩ := haux.1 w (by omega)
      simp only [nextYA, DoubleAndAdd.yA, DoubleAndAdd.xR]
      rw [hxw, hxA_last, hpw, hl1w, hl2w]
      linear_combination -hYIw - 2 * haccy w + 2 * hexity

/--
The chain induction of one piece over cleaned row facts: `dR r` are the per-row cell
values, `zV r` the running sum values. Splitting this from `soundness` keeps each
declaration within the elaboration budget.
-/
private theorem soundness_aux (G : Generators) (w : ℕ)
    (dR : ℕ → DoubleAndAddRow Fp) (zV : ℕ → Fp) (piece xA : Fp)
    (hxA0 : (dR 0).xA = xA)
    (hz0 : zV 0 = piece)
    (hL : ∀ r, r < w + 1 → ∃ m : ℕ, m < 2 ^ K ∧
      (if r = w then zV r else zV r - 2 ^ K * zV (r + 1)) = (m : Fp) ∧
      (dR r).xP = (G.S m).x ∧
      DoubleAndAdd.yA (dR r) * (2 : Fp)⁻¹
        - (dR r).lambda1 * ((dR r).xA - (dR r).xP) = (G.S m).y)
    (hG : ∀ r, r < w →
      ((dR r).lambda2 * (dR r).lambda2
        = (dR (r + 1)).xA + ((dR r).lambda1 * (dR r).lambda1 - (dR r).xA - (dR r).xP)
          + (dR r).xA) ∧
      4 * (dR r).lambda2 * ((dR r).xA - (dR (r + 1)).xA)
        = 2 * DoubleAndAdd.yA (dR r) + 2 * DoubleAndAdd.yA (dR (r + 1))) :
    ∃ ms : ℕ → ℕ,
      (∀ r, ms r < 2 ^ K) ∧
      piece = ((∑ r ∈ Finset.range (w + 1), ms r * 2 ^ (K * r) : ℕ) : Fp) ∧
      Vector.ofFn (fun r : Fin (w + 1) => zV r.val) =
        Vector.ofFn (fun r : Fin (w + 1) =>
          ((∑ j ∈ Finset.range (w + 1 - r.val), ms (r.val + j) * 2 ^ (K * j) : ℕ) : Fp)) ∧
      (dR 0).xA = xA ∧
      (dR w).xP = (G.S (ms w)).x ∧
      DoubleAndAdd.yA (dR w) * (2 : Fp)⁻¹
        - (dR w).lambda1 * ((dR w).xA - (dR w).xP) = (G.S (ms w)).y ∧
      ∀ A : Point Fp, A.OnCurve → A.x = xA →
        2 * A.y = DoubleAndAdd.yA (dR 0) →
        ∀ B, Specs.Sinsemilla.hashToPoint G.S A
            ((List.range w).map ms) = some B →
          (dR w).xA = B.x ∧ 2 * B.y = DoubleAndAdd.yA (dR w) := by
  -- choose the word values
  have hLE : ∀ r : Fin (w + 1), ∃ m : ℕ, m < 2 ^ K ∧
      (if r.val = w then zV r.val else zV r.val - 2 ^ K * zV (r.val + 1)) = (m : Fp) ∧
      (dR r.val).xP = (G.S m).x ∧
      DoubleAndAdd.yA (dR r.val) * (2 : Fp)⁻¹
        - (dR r.val).lambda1 * ((dR r.val).xA - (dR r.val).xP) = (G.S m).y :=
    fun r => hL r.val r.isLt
  choose mf hmf_lt hmf_word hmf_x hmf_y using hLE
  obtain ⟨ms, hms⟩ : ∃ ms : ℕ → ℕ, ms = fun r =>
      if h : r < w + 1 then mf ⟨r, h⟩ else 0 := ⟨_, rfl⟩
  have hms_lt : ∀ r, ms r < 2 ^ K := by
    intro r
    simp only [hms]
    split_ifs
    · exact hmf_lt _
    · norm_num [K]
  have hms_at : ∀ r (hr : r < w + 1), ms r = mf ⟨r, hr⟩ := by
    intro r hr
    simp only [hms]
    rw [dif_pos hr]
  -- recombination of the piece from its words
  have hpiece : piece
      = ((∑ r ∈ Finset.range (w + 1), ms r * 2 ^ (K * r) : ℕ) : Fp) := by
    rw [← hz0]
    have key : ∀ r, r ≤ w →
        zV 0 = ((∑ j ∈ Finset.range r, ms j * 2 ^ (K * j) : ℕ) : Fp)
          + zV r * ((2 ^ (K * r) : ℕ) : Fp) := by
      intro r hr
      induction r with
      | zero => simp
      | succ v ih =>
        have h := hmf_word ⟨v, by omega⟩
        rw [if_neg (show ¬ (⟨v, by omega⟩ : Fin (w + 1)).val = w by simp; omega)] at h
        rw [ih (by omega), Finset.sum_range_succ]
        rw [← hms_at v (by omega)] at h
        push_cast
        rw [show K * (v + 1) = K * v + K by ring]
        push_cast [pow_add]
        linear_combination ((2 : Fp) ^ (K * v)) * h
    have hlast : zV w = ((ms w : ℕ) : Fp) := by
      have h := hmf_word ⟨w, by omega⟩
      rw [if_pos rfl] at h
      rw [hms_at w (by omega)]
      exact h
    rw [key w (by omega), hlast, Finset.sum_range_succ]
    push_cast
    ring
  refine ⟨ms, hms_lt, hpiece, ?_, hxA0, ?_, ?_, ?_⟩
  · -- the running sums equal the suffix recombinations
    have hword : ∀ s, s < w → zV s = (ms s : Fp) + 2 ^ K * zV (s + 1) := by
      intro s hs
      have h := hmf_word ⟨s, by omega⟩
      rw [if_neg (show ¬ (⟨s, by omega⟩ : Fin (w + 1)).val = w by simp; omega)] at h
      rw [← hms_at s (by omega)] at h
      linear_combination h
    have hlast : zV w = (ms w : Fp) := by
      have h := hmf_word ⟨w, by omega⟩
      rw [if_pos rfl] at h
      rw [hms_at w (by omega)]
      exact h
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    have h := chain_eq_suffix_sum zV ms hword hlast (w - i) i (by omega)
    rw [show w - i + 1 = w + 1 - i from by omega] at h
    exact h
  · rw [hms_at w (by omega)]
    exact hmf_x ⟨w, by omega⟩
  · rw [hms_at w (by omega)]
    exact hmf_y ⟨w, by omega⟩
  -- the chain invariant over message prefixes
  intro A hAon hAx hAyA B hchain
  have hinv : ∀ r, r ≤ w → ∀ Ar : Point Fp,
      Specs.Sinsemilla.hashToPoint G.S A ((List.range r).map ms) = some Ar →
      (dR r).xA = Ar.x ∧ 2 * Ar.y = DoubleAndAdd.yA (dR r) := by
    intro r
    induction r with
    | zero =>
      intro _ Ar hAr
      rw [show ((List.range 0).map ms) = ([] : List ℕ) from rfl,
        Specs.Sinsemilla.hashToPoint_nil] at hAr
      obtain rfl : A = Ar := Option.some.inj hAr
      exact ⟨hxA0.trans hAx.symm, hAyA⟩
    | succ r ih =>
      intro hr Ar hAr
      rw [List.range_succ] at hAr
      simp only [List.map_append, List.map_cons, List.map_nil] at hAr
      rw [Specs.Sinsemilla.hashToPoint_concat] at hAr
      cases hpre : Specs.Sinsemilla.hashToPoint G.S A ((List.range r).map ms) with
      | none =>
        rw [hpre] at hAr
        simp at hAr
      | some Ap =>
        rw [hpre] at hAr
        replace hAr : Specs.Sinsemilla.step G.S (ms r) Ap = some Ar := hAr
        obtain ⟨hxAr, hyAr⟩ := ih (by omega) Ap hpre
        have hxw := hmf_x ⟨r, by omega⟩
        have hyw := hmf_y ⟨r, by omega⟩
        rw [← hms_at r (by omega)] at hxw hyw
        obtain ⟨hsec, hyck⟩ := hG r (by omega)
        have hyAr' := hyAr
        simp only [DoubleAndAdd.yA, DoubleAndAdd.xR] at hyAr'
        have hyw2 := double_halved hyw
        have hpin := step_coordinates_of_constraints G.S hAr
          (xp := (dR r).xP) (lambda1 := (dR r).lambda1) (lambda2 := (dR r).lambda2)
          (xa' := (dR (r + 1)).xA)
          (YA' := DoubleAndAdd.yA (dR (r + 1)))
          (by linear_combination hyw2 + hyAr + 2 * (dR r).lambda1 * hxAr)
          hxw
          (by linear_combination hyAr'
            + 2 * ((dR r).lambda1 + (dR r).lambda2) * hxAr)
          (by linear_combination hsec)
          (by linear_combination hyck - 4 * (dR r).lambda2 * hxAr - 2 * hyAr)
        exact ⟨hpin.1, hpin.2.symm⟩
  exact hinv w (by omega) B hchain

theorem soundness (G : Generators) (w : ℕ) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G w) (fun _ _ => True)
      (Spec G w) := by
  circuit_proof_start [Gate.circuit, Gate.Spec, generatorTable]
  obtain ⟨h_copy, h_lookups, h_gates⟩ := h_holds
  simp only [Vector.getElem_append, Vector.getElem_mapRange,
    circuit_norm] at h_lookups h_gates ⊢
  obtain ⟨dR, hdR⟩ : ∃ dR : ℕ → DoubleAndAddRow Fp, dR = fun r =>
      { xA := if _ : r = 0 then input_xA
          else env.get (i₀ + 1 + w + (w + 1) + (w + 1) + (w + 1) + (r - 1)),
        xP := env.get (i₀ + 1 + w + r),
        lambda1 := env.get (i₀ + 1 + w + (w + 1) + r),
        lambda2 := env.get (i₀ + 1 + w + (w + 1) + (w + 1) + r) } := ⟨_, rfl⟩
  obtain ⟨zV, hzV⟩ : ∃ zV : ℕ → Fp, zV = fun r =>
      if _ : r < 1 then env.get i₀ else env.get (i₀ + 1 + (r - 1)) := ⟨_, rfl⟩
  have hL : ∀ r, r < w + 1 → ∃ m : ℕ, m < 2 ^ K ∧
      (if r = w then zV r else zV r - 2 ^ K * zV (r + 1)) = (m : Fp) ∧
      (dR r).xP = (G.S m).x ∧
      DoubleAndAdd.yA (dR r) * (2 : Fp)⁻¹
        - (dR r).lambda1 * ((dR r).xA - (dR r).xP) = (G.S m).y := by
    intro r hr
    obtain ⟨m, hm, hidx, hx, hy⟩ := h_lookups ⟨r, hr⟩
    simp only [DoubleAndAdd.yA, DoubleAndAdd.xR, apply_dite (Expression.eval env),
      h_input.2.1, circuit_norm] at hidx hx hy
    refine ⟨m, hm, ?_, by simp only [hdR]; exact hx, ?_⟩
    · simp only [hzV]
      rcases Nat.lt_or_ge r 1 with h0 | h0
      · obtain rfl : r = 0 := by omega
        split_ifs at hidx ⊢ <;> try omega
        all_goals try simp only [circuit_norm, List.getElem_cons_zero,
          show ∀ a : ℕ, a + 1 - 1 = a from fun _ => rfl, Nat.add_zero] at hidx
        all_goals try simp only [show ∀ a : ℕ, a + 1 - 1 = a from fun _ => rfl,
          Nat.add_zero]
        all_goals linear_combination hidx
      · split_ifs at hidx ⊢ <;> try omega
    · simp only [hdR, DoubleAndAdd.yA, DoubleAndAdd.xR]
      linear_combination hy
  have hG : ∀ r, r < w →
      ((dR r).lambda2 * (dR r).lambda2
        = (dR (r + 1)).xA + ((dR r).lambda1 * (dR r).lambda1 - (dR r).xA - (dR r).xP)
          + (dR r).xA) ∧
      4 * (dR r).lambda2 * ((dR r).xA - (dR (r + 1)).xA)
        = 2 * DoubleAndAdd.yA (dR r) + 2 * DoubleAndAdd.yA (dR (r + 1)) := by
    intro r hr
    obtain ⟨hsec, hy⟩ := h_gates ⟨r, hr⟩
    simp only [Gate.yLhs, Gate.yRhs, Gate.qS3, DoubleAndAdd.yA, DoubleAndAdd.xR,
      apply_dite (Expression.eval env), h_input.2.1, circuit_norm] at hsec hy
    constructor
    · simp only [hdR]
      linear_combination hsec
    · simp only [hdR, DoubleAndAdd.yA, DoubleAndAdd.xR]
      linear_combination hy
  have haux := soundness_aux G w dR zV input_piece input_xA
    (by simp only [hdR]; rfl) (by simp only [hzV]; exact h_copy) hL hG
  have hOut : Vector.map (Expression.eval env)
      (Vector.cast (Nat.add_comm 1 w)
        ((#v[Expression.var ⟨i₀⟩] : Vector (Expression Fp) 1)
          ++ (Vector.mapRange w (fun i => Expression.var ⟨i₀ + 1 + i⟩) :
              Vector (Expression Fp) w)))
      = Vector.ofFn (fun r : Fin (w + 1) => zV r.val) := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_map, Vector.getElem_ofFn]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [Vector.getElem_cast, Vector.getElem_append, hzV,
        apply_dite (Expression.eval env), Nat.lt_one_iff, circuit_norm]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      simp only [Vector.getElem_cast, Vector.getElem_append, Vector.getElem_mapRange, hzV,
        Nat.succ_ne_zero, Nat.lt_one_iff, dite_false, circuit_norm]
  simpa only [hdR, hzV, apply_ite (Expression.eval env), dite_eq_ite,
    eq_self_iff_true, if_true, Nat.add_zero, h_input.2.1, hOut, circuit_norm] using haux

def circuit (G : Generators) (w : ℕ) :
    GeneralFormalCircuit.WithHint Fp Input (Output (w + 1)) where
  main := main G w
  elaborated := elaborated G w
  Spec := Spec G w
  ProverAssumptions := ProverAssumptions G w
  ProverSpec := ProverSpec G w
  soundness := soundness G w
  completeness := completeness G w

end HashPiece

/-!
### Piece chaining (`hash_to_point.rs::hash_all_pieces`)

The pieces of a message are chained by recursion over the list of per-piece word
counts. Each level hashes one piece and emits the gate that completes the piece's last
double-and-add step, pairing the piece's last row with the *next* level's exposed first
row: `q_s2 = 0` between pieces, `q_s2 = 2` for the final gate, whose `next` row is the
dummy row holding the witnessed final `y_a` in the `λ₁` cell (`hash_all_pieces`). The
gate polynomial `2·Y_A(cur) + (2 - q_s3)·Y_A(next) + q_s3·2·λ₁(next)` uniformly selects
the right entering-`Y_A` expression of the next level, captured by `enterYA`.
-/

namespace Chain

/-- Inputs of the chain tail over `k` remaining pieces: the piece cells, the entering
accumulator `x_A` cell, and the entering accumulator `y` as a prover hint. -/
structure Input (k : ℕ) (F : Type) where
  pieces : Vector F k
  xA : F
  yA : UnconstrainedDepNative field F
deriving CircuitType

instance (k : ℕ) : Inhabited (Var (Input k) Fp) :=
  ⟨{ pieces := default, xA := default, yA := default }⟩

/-- Per-piece running-sum lengths: piece `i` of width `nᵢ` produces `nᵢ + 1`
running-sum cells (`z₀..z_{nᵢ}`). -/
def zLengths (ns : List ℕ) : List ℕ := ns.map (· + 1)

/-- Outputs: the hash point, the first gate row of this level (the previous level
emits the gate pairing its last row with this row; at the end of the message this is
the dummy row carrying the witnessed final `y_a` in its `λ₁` cell), and the full
per-piece running sums `zs` (`hash_to_point` returns all running sums; consumers read
specific cells, e.g. `MerkleCRH` projects each piece's `z_1` via `Z1s`). -/
structure Output (ns : List ℕ) (F : Type) where
  point : Point F
  first : DoubleAndAddRow F
  zs : HVec (zLengths ns) F
deriving ProvableStruct

/-- The entering accumulator `2·y` of a level, as derived by the preceding gate from
the level's first row: the `Y_A` expression for in-message rows, twice the witnessed
`y_a` cell for the final dummy row. -/
def enterYA {F : Type} [Add F] [Sub F] [Mul F] [OfNat F 2]
    (isFinal : Bool) (row : DoubleAndAddRow F) : F :=
  if isFinal then 2 * row.lambda1 else DoubleAndAdd.yA row

/-- The pieces decompose into the given flat chunk list (`K`-bit words, little-endian
within each piece, `ns[i] + 1` words for piece `i`). -/
def PieceChunks : (ns : List ℕ) → Vector Fp ns.length → List ℕ → Prop
  | [], _, chunks => chunks = []
  | n :: rest, pieces, chunks => ∃ ms : ℕ → ℕ,
      (∀ r, ms r < 2 ^ K) ∧
      pieces[0] = ((∑ r ∈ Finset.range (n + 1), ms r * 2 ^ (K * r) : ℕ) : Fp) ∧
      ∃ tailChunks, chunks = (List.range (n + 1)).map ms ++ tailChunks ∧
        PieceChunks rest pieces.tail tailChunks

/-- The honest chunk values of the pieces. -/
def honestChunks : (ns : List ℕ) → Vector Fp ns.length → List ℕ
  | [], _ => []
  | n :: rest, pieces =>
    (List.range (n + 1)).map (pieceWord pieces[0]) ++ honestChunks rest pieces.tail

/-- Each piece value fits in `K·(ns[i] + 1)` bits. -/
def PieceBounds : (ns : List ℕ) → Vector Fp ns.length → Prop
  | [], _ => True
  | n :: rest, pieces =>
    ZMod.val pieces[0] < 2 ^ (K * (n + 1)) ∧
      PieceBounds rest pieces.tail

/-- The honest chunk values realize the `PieceChunks` relation when the pieces are in
range: each piece is the recombination of its `K`-bit words (`piece_recombine`). -/
theorem pieceChunks_honestChunks : (ns : List ℕ) → (pieces : Vector Fp ns.length) →
    PieceBounds ns pieces → PieceChunks ns pieces (honestChunks ns pieces)
  | [], _, _ => rfl
  | n :: rest, pieces, hbounds => by
    obtain ⟨hb0, hbrest⟩ := hbounds
    refine ⟨pieceWord pieces[0], fun r => HashPiece.pieceWord_lt _ _, ?_,
      honestChunks rest pieces.tail, rfl, pieceChunks_honestChunks rest pieces.tail hbrest⟩
    exact HashPiece.piece_recombine pieces[0] (n + 1) hb0

theorem pieceChunks_bound {ns : List ℕ} {pieces : Vector Fp ns.length}
    {chunks : List ℕ} (h : PieceChunks ns pieces chunks) :
    ∀ m ∈ chunks, m < 2 ^ K := by
  induction ns generalizing chunks with
  | nil =>
      intro m hm
      simp only [PieceChunks] at h
      subst h
      simp at hm
  | cons n rest ih =>
      simp only [PieceChunks] at h
      obtain ⟨ms, hms, _, tailChunks, hchunks, htail⟩ := h
      intro m hm
      rw [hchunks] at hm
      simp only [List.mem_append, List.mem_map, List.mem_range] at hm
      rcases hm with ⟨r, hr, rfl⟩ | hm
      · exact hms r
      · exact ih htail m hm

/-- Each exposed `z_1` cell is the recombination of its piece's chunks with the first
word stripped (anchored to the same flat chunk list as `PieceChunks`). -/
def Z1Facts : (ns : List ℕ) → List ℕ → Vector Fp ns.length → Prop
  | [], _, _ => True
  | n :: rest, chunks, z1s =>
    z1s[0] = ((∑ j ∈ Finset.range n, chunks.getD (j + 1) 0 * 2 ^ (K * j) : ℕ) : Fp) ∧
      Z1Facts rest (chunks.drop (n + 1)) z1s.tail

/-- The first piece's `z_1` fact, extracted from a folded `Z1Facts`. -/
theorem z1Facts_getElem_zero {a : ℕ} {rest : List ℕ} {chunks : List ℕ}
    {z1s : Vector Fp (a :: rest).length} (h : Z1Facts (a :: rest) chunks z1s) :
    z1s[0] = ((∑ j ∈ Finset.range a, chunks.getD (j + 1) 0 * 2 ^ (K * j) : ℕ) : Fp) := by
  simp only [Z1Facts] at h
  exact h.1

/-- The second piece's `z_1` fact, indexed directly as `z1s[1]` rather than the
`z1s.tail[0]` spelling the recursive `Z1Facts` produces. Stated for an abstract vector,
so the `tail → [1]` conversion happens here (cheaply) instead of on a concrete
`hash_to_point` output vector, where the same `getElem`/`tail` defeq blows up. -/
theorem z1Facts_getElem_one {a b : ℕ} {rest : List ℕ} {chunks : List ℕ}
    {z1s : Vector Fp (a :: b :: rest).length} (h : Z1Facts (a :: b :: rest) chunks z1s) :
    z1s[1]'(by simp) = ((∑ j ∈ Finset.range b,
        (chunks.drop (a + 1)).getD (j + 1) 0 * 2 ^ (K * j) : ℕ) : Fp) := by
  simp only [Z1Facts] at h
  obtain ⟨-, h2, -⟩ := h
  exact (Vector.getElem_tail (show (0 : ℕ) < (a :: b :: rest).length - 1 by simp)).symm.trans h2

/-- The honest `z_1` values. -/
def Z1sHonest : (ns : List ℕ) → Vector Fp ns.length → Vector Fp ns.length → Prop
  | [], _, _ => True
  | _ :: rest, pieces, z1s =>
    z1s[0] = pieceZ pieces[0] 1 ∧ Z1sHonest rest pieces.tail z1s.tail

/-- Each exposed running-sum vector is the per-row suffix recombination of its piece's
chunks (anchored to the same flat chunk list as `PieceChunks`). The `z₁` cell is the
`r = 1` entry, so `ZsFacts` refines `Z1Facts`. -/
def ZsFacts : (ns : List ℕ) → List ℕ → HVec (zLengths ns) Fp → Prop
  | [], _, _ => True
  | n :: rest, chunks, zs =>
    HVec.head zs = Vector.ofFn (fun r : Fin (n + 1) =>
      ((∑ j ∈ Finset.range (n + 1 - r.val),
        chunks.getD (r.val + j) 0 * 2 ^ (K * j) : ℕ) : Fp)) ∧
      ZsFacts rest (chunks.drop (n + 1)) (HVec.tail zs)

/-- The honest running-sum vectors: each piece's vector holds `z₀..z_{nᵢ}`. -/
def ZsHonest : (ns : List ℕ) → Vector Fp ns.length → HVec (zLengths ns) Fp → Prop
  | [], _, _ => True
  | n :: rest, pieces, zs =>
    HVec.head zs = Vector.ofFn (fun r : Fin (n + 1) => pieceZ pieces[0] r.val) ∧
      ZsHonest rest pieces.tail (HVec.tail zs)

/-- Project the per-piece `z₁` cells out of the full running sums: piece `i`'s `z₁` is
the `r = 1` running-sum cell (`zs[i][1]`), or `0` for a width-0 piece. This is the
`MerkleCRH`/`Z1s` view of `hash_to_point`'s running sums `zs`. -/
def z1sOfZs {F : Type} [Zero F] : (ns : List ℕ) → HVec (zLengths ns) F → Vector F ns.length
  | [], _ => #v[]
  | n :: rest, zs => .listCons
    (if h : 1 < n + 1 then (HVec.head zs)[1]'h else (0 : F))
    (z1sOfZs rest (HVec.tail zs))

@[simp] theorem z1sOfZs_getElem_zero {F : Type} [Zero F] (n : ℕ) (rest : List ℕ)
    (zs : HVec (zLengths (n :: rest)) F) :
    (z1sOfZs (n :: rest) zs)[0]'(by simp) =
      if h : 1 < n + 1 then (HVec.head zs)[1]'h else (0 : F) := by
  simp [z1sOfZs, Vector.listCons]

theorem z1sOfZs_tail {F : Type} [Zero F] (n : ℕ) (rest : List ℕ)
    (zs : HVec (zLengths (n :: rest)) F) :
    (z1sOfZs (n :: rest) zs).tail = z1sOfZs rest (HVec.tail zs) := by
  simp only [z1sOfZs, Vector.listCons]
  ext i hi
  simp; rfl

theorem z1sOfZs_getElem_succ {F : Type} [Zero F] (n : ℕ) (rest : List ℕ)
    (zs : HVec (zLengths (n :: rest)) F) (k : ℕ) (hk : k + 1 < (n :: rest).length) :
    (z1sOfZs (n :: rest) zs)[k + 1]'hk = (z1sOfZs rest (HVec.tail zs))[k]'(by simpa using hk) := by
  simp [z1sOfZs, Vector.listCons]

/-- The `z₁` projection of an honest/sound running-sum tower satisfies `Z1Facts`: each
`z₁` cell is the `r = 1` suffix recombination, exactly the `ZsFacts` entry at `r = 1`. -/
theorem z1Facts_of_zsFacts : (ns : List ℕ) → (chunks : List ℕ) →
    (zs : HVec (zLengths ns) Fp) → ZsFacts ns chunks zs →
    Z1Facts ns chunks (z1sOfZs ns zs)
  | [], _, _, _ => trivial
  | n :: rest, chunks, zs, h => by
    obtain ⟨hhead, htail⟩ := h
    refine ⟨?_, ?_⟩
    · rw [z1sOfZs_getElem_zero]
      by_cases hn : 1 < n + 1
      · simp only [dif_pos hn]
        rw [hhead]
        simp only [Vector.getElem_ofFn]
        congr 1
        have hsub : n + 1 - 1 = n := by omega
        rw [hsub]
        apply Finset.sum_congr rfl
        intro j _
        rw [Nat.add_comm 1 j]
      · simp only [dif_neg hn]
        have hn0 : n = 0 := by omega
        subst hn0
        simp
    · rw [z1sOfZs_tail]
      exact z1Facts_of_zsFacts rest (chunks.drop (n + 1)) (HVec.tail zs) htail

/-- The `z₁` projection of an honest running-sum tower satisfies `Z1sHonest` (the
width-0 case uses `PieceBounds`: a single-word piece has `z₁ = 0`). -/
theorem z1sHonest_of_zsHonest : (ns : List ℕ) → (pieces : Vector Fp ns.length) →
    (zs : HVec (zLengths ns) Fp) → PieceBounds ns pieces → ZsHonest ns pieces zs →
    Z1sHonest ns pieces (z1sOfZs ns zs)
  | [], _, _, _, _ => trivial
  | n :: rest, pieces, zs, hb, h => by
    obtain ⟨hhead, htail⟩ := h
    obtain ⟨hb0, hbrest⟩ := hb
    refine ⟨?_, ?_⟩
    · rw [z1sOfZs_getElem_zero]
      by_cases hn : 1 < n + 1
      · simp only [dif_pos hn]
        rw [hhead]
        simp [Vector.getElem_ofFn]
      · simp only [dif_neg hn]
        have hn0 : n = 0 := by omega
        subst hn0
        refine (?_ : pieceZ pieces[0] 1 = 0).symm
        simp only [pieceZ]
        rw [Nat.div_eq_of_lt hb0]
        simp
    · rw [z1sOfZs_tail]
      exact z1sHonest_of_zsHonest rest pieces.tail (HVec.tail zs) hbrest htail

/-- `eval` commutes with the `z₁` projection (it is a pointwise selection of running-sum
cells), letting a `zs`-projecting `hash_to_point` view bridge its evaluated output to the
running sums. -/
theorem eval_z1sOfZs {F : Type} [FiniteField F] (env : Environment F) : (ns : List ℕ) →
    (zs : Var (HVec (zLengths ns)) F) →
    (eval env (z1sOfZs ns zs) : Vector F ns.length) = z1sOfZs ns (eval env zs)
  | [], zs => by
    apply Vector.ext
    intro i hi
    simp at hi
  | n :: rest, zs => by
    have htail := eval_z1sOfZs env rest (HVec.tail zs)
    rw [HVec.eval_tail] at htail
    apply Vector.ext
    intro i hi
    rw [ProvableType.eval_fields, Vector.getElem_map]
    rcases i with _ | k
    · rw [z1sOfZs_getElem_zero, z1sOfZs_getElem_zero]
      by_cases hn : 1 < n + 1
      · simp only [dif_pos hn]
        rw [ProvableType.getElem_eval_fields, HVec.eval_head]
        rfl
      · simp only [dif_neg hn]
        rfl
    · rw [z1sOfZs_getElem_succ, z1sOfZs_getElem_succ, ProvableType.getElem_eval_fields,
        eval_z1sOfZs env rest (HVec.tail zs), HVec.eval_tail]
      rfl

def Spec (G : Generators) (ns : List ℕ) (input : Value (Input ns.length) Fp)
    (output : Value (Output ns) Fp) (_ : ProverData Fp) : Prop :=
  output.first.xA = input.xA ∧
  ∃ chunks : List ℕ, PieceChunks ns input.pieces chunks ∧
    ZsFacts ns chunks output.zs ∧
    ∀ A : Point Fp, A.OnCurve → A.x = input.xA →
      2 * A.y = enterYA ns.isEmpty output.first →
      ∀ B, Specs.Sinsemilla.hashToPoint G.S A chunks = some B →
        output.point.x = B.x ∧ output.point.y = B.y

def ProverAssumptions (G : Generators) (ns : List ℕ)
    (input : ProverValue (Input ns.length) Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  PieceBounds ns input.pieces ∧
  ∃ (A B : Point Fp), A.OnCurve ∧ A.x = input.xA ∧ A.y = input.yA ∧
    Specs.Sinsemilla.hashToPoint G.S A (honestChunks ns input.pieces) = some B

def ProverSpec (G : Generators) (ns : List ℕ)
    (input : ProverValue (Input ns.length) Fp)
    (output : ProverValue (Output ns) Fp) (_ : ProverHint Fp) : Prop :=
  output.first.xA = input.xA ∧
  ZsHonest ns input.pieces output.zs ∧
  ∀ A : Point Fp, A ≠ 0 → A.x = input.xA → A.y = input.yA →
    enterYA ns.isEmpty output.first = 2 * A.y ∧
    ∀ B, Specs.Sinsemilla.hashToPoint G.S A
        (honestChunks ns input.pieces) = some B →
      output.point.x = B.x ∧ output.point.y = B.y

/-! #### The empty tail: the final dummy row -/

namespace Nil

def main (input : Var (Input 0) Fp) : Circuit Fp (Var (Output []) Fp) := do
  let yFin ← witnessNative fun env => input.yA env
  return {
    point := { x := input.xA, y := yFin },
    first := { xA := input.xA, xP := 0, lambda1 := yFin, lambda2 := 0 },
    zs := HVec.nil }

instance elaborated : ElaboratedCircuit Fp (Input 0) (Output []) main := by
  elaborate_circuit

theorem soundness (G : Generators) :
    GeneralFormalCircuit.WithHint.Soundness Fp main (fun _ _ => True)
      (Spec G []) := by
  circuit_proof_start [PieceChunks, ZsFacts, enterYA]
  refine ⟨[], rfl, ?_⟩
  intro A hAon hAx hAy B hB
  have hAy' : 2 * A.y = 2 * env.get i₀ := by simpa using hAy
  rw [Specs.Sinsemilla.hashToPoint_nil] at hB
  obtain rfl : A = B := Option.some.inj hB
  exact ⟨hAx.symm, (mul_left_cancel₀ HashPiece.two_ne_zero_Fp hAy').symm⟩

theorem completeness (G : Generators) :
    GeneralFormalCircuit.WithHint.Completeness Fp main
      (ProverAssumptions G []) (ProverSpec G []) := by
  circuit_proof_start [honestChunks, ZsHonest, enterYA]
  intro A hAon hAx hAy
  constructor
  · simp only [List.isEmpty_nil, if_true]
    rw [h_env, ← hAy]
  · intro B hB
    rw [Specs.Sinsemilla.hashToPoint_nil] at hB
    obtain rfl : A = B := Option.some.inj hB
    exact ⟨hAx.symm, by rw [h_env, ← hAy]⟩

def circuit (G : Generators) :
    GeneralFormalCircuit.WithHint Fp (Input 0) (Output []) where
  main
  elaborated
  Spec := Spec G []
  ProverAssumptions := ProverAssumptions G []
  ProverSpec := ProverSpec G []
  soundness := soundness G
  completeness := completeness G

end Nil

theorem z1Facts_head_sum {n : ℕ} (ms : ℕ → ℕ) (tailChunks : List ℕ) :
    (∑ j ∈ Finset.range n,
        ((List.range (n + 1)).map ms ++ tailChunks).getD (j + 1) 0 * 2 ^ (K * j))
      = ∑ j ∈ Finset.range n, ms (j + 1) * 2 ^ (K * j) := by
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < n := Finset.mem_range.mp hj
  rw [List.getD_append _ _ _ _ (by simp; omega),
    List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem chunks_drop_append {n : ℕ} (ms : ℕ → ℕ) (tailChunks : List ℕ) :
    ((List.range (n + 1)).map ms ++ tailChunks).drop (n + 1) = tailChunks :=
  List.drop_left' (by simp)

/-- A head-piece chunk index resolves to its word value. -/
theorem chunks_head_getD {n : ℕ} (ms : ℕ → ℕ) (tailChunks : List ℕ) (k : ℕ) (hk : k < n + 1) :
    ((List.range (n + 1)).map ms ++ tailChunks).getD k 0 = ms k := by
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
  simp

/-! #### One piece plus the recursive tail -/

/-- Number of local witnesses of the chain tail: the final `y_a`, plus per piece the
`hash_piece` cells (`z₀`, the `z` tail, and the four row-cell columns). -/
def chainLength : List ℕ → ℕ
  | [] => 1
  | n :: rest => 1 + (n + (n + 1 + (n + 1 + (n + 1 + (n + 1))))) + chainLength rest

lemma chainLength_cons (n : ℕ) (rest : List ℕ) :
    chainLength (n :: rest) = 5*(n + 1) + chainLength rest := by
  simp +arith [chainLength]

lemma chainLength_def (list : List ℕ) :
    chainLength list = 5*list.sum + 5*list.length + 1 := by
  induction list with
  | nil => rfl
  | cons n rest ih => simp_all +arith [chainLength_cons]

namespace Cons

def main (G : Generators) (n : ℕ) (rest : List ℕ)
    (tail : GeneralFormalCircuit.WithHint Fp (Input rest.length) (Output rest))
    (input : Var (Input (rest.length + 1)) Fp) :
    Circuit Fp (Var (Output (n :: rest)) Fp) := do
  let out ← HashPiece.circuit G n
    { piece := input.pieces[0], xA := input.xA, yA := input.yA }
  let tailOut ← tail
    { pieces := Vector.cast (by omega) input.pieces.tail,
      xA := out.xANext, yA := out.yANext }
  Gate.circuit { qS2 := if rest.isEmpty then 2 else 0 }
    { cur := out.last, next := tailOut.first }
  return {
    point := tailOut.point,
    first := out.first,
    zs := HVec.cons out.zs tailOut.zs }

/-- Hand-written elaboration data: `elaborate_circuit` cannot derive the local length
through the recursive tail, whose bundle is a variable here; the constant-length and
no-channels facts are threaded through the chain recursion. -/
@[reducible] def elaborated (G : Generators) (n : ℕ) (rest : List ℕ)
    (tail : GeneralFormalCircuit.WithHint Fp (Input rest.length) (Output rest))
    (tailLen : ℕ) (htail : ∀ inp, tail.localLength inp = tailLen)
    (hcwg : tail.channelsWithGuarantees = [])
    (_hcwr : tail.channelsWithRequirements = []) :
    ElaboratedCircuit Fp (Input (rest.length + 1)) (Output (n :: rest))
      (main G n rest tail) where
  localLength input := (HashPiece.circuit G n).localLength
      { piece := input.pieces[0], xA := input.xA, yA := input.yA } + tailLen
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, htail, Gate.circuit]
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    dsimp only [main]
    simp only [circuit_norm, seval, HashPiece.circuit, Gate.circuit, hcwg]
    try trivial

/-- The gate's `y`-polynomial right-hand side computes twice the entering-`Y_A`
expression of the next level, for both the boundary (`q_s2 = 0`) and final
(`q_s2 = 2`) selector values. -/
private theorem gate_yRhs_enterYA (b : Bool) (row : Gate.Row Fp) :
    Gate.yRhs { qS2 := if b = true then (2 : Fp) else 0 } row
      = 2 * DoubleAndAdd.yA row.cur + 2 * enterYA b row.next := by
  cases b <;> (simp [Gate.yRhs, Gate.qS3, enterYA]; try ring)

/--
The chain glue of one level over cleaned values: the piece's prefix contract, the
gate completing its last step (via `step_coordinates_of_constraints`), and the tail's chain contract
compose to the level's chain contract.
-/
private theorem soundness_aux (G : Generators) (n : ℕ) (isFinal : Bool)
    (ms : ℕ → ℕ)
    (hms : ∀ r, ms r < 2 ^ K)
    {first last tailFirst : DoubleAndAddRow Fp} {xAin : Fp}
    (hlast_xP : last.xP = (G.S (ms n)).x)
    (hlast_yp : DoubleAndAdd.yA last * (2 : Fp)⁻¹
      - last.lambda1 * (last.xA - last.xP) = (G.S (ms n)).y)
    (hchain_piece : ∀ A : Point Fp, A.OnCurve → A.x = xAin →
      2 * A.y = DoubleAndAdd.yA first →
      ∀ B, Specs.Sinsemilla.hashToPoint G.S A
          ((List.range n).map ms) = some B →
        last.xA = B.x ∧ 2 * B.y = DoubleAndAdd.yA last)
    (hsec : last.lambda2 * last.lambda2
      = tailFirst.xA + DoubleAndAdd.xR last + last.xA)
    (hyck : Gate.yLhs { cur := last, next := tailFirst }
      = Gate.yRhs { qS2 := if isFinal = true then (2 : Fp) else 0 }
          { cur := last, next := tailFirst })
    {xATail : Fp} (htfxA : tailFirst.xA = xATail)
    (tailChunks : List ℕ) {pointX pointY : Fp}
    (htail_chain : ∀ A : Point Fp, A.OnCurve → A.x = xATail →
      2 * A.y = enterYA isFinal tailFirst →
      ∀ B, Specs.Sinsemilla.hashToPoint G.S A tailChunks = some B →
        pointX = B.x ∧ pointY = B.y) :
    ∀ A : Point Fp, A.OnCurve → A.x = xAin →
      2 * A.y = DoubleAndAdd.yA first →
      ∀ B, Specs.Sinsemilla.hashToPoint G.S A
          ((List.range (n + 1)).map ms ++ tailChunks) = some B →
        pointX = B.x ∧ pointY = B.y := by
  intro A hAon hAx hAyA B hB
  have hAvalid : A.Valid := Or.inl hAon
  have hA0 : A ≠ 0 := Point.ne_zero_of_onCurve hAon
  -- split the chain at the piece boundary
  rw [Specs.Sinsemilla.hashToPoint_append] at hB
  cases hpre : Specs.Sinsemilla.hashToPoint G.S A
      ((List.range (n + 1)).map ms) with
  | none =>
    rw [hpre] at hB
    simp at hB
  | some B₁ =>
    rw [hpre] at hB
    replace hB : Specs.Sinsemilla.hashToPoint G.S B₁ tailChunks = some B := hB
    -- peel the piece's last word
    rw [List.range_succ] at hpre
    simp only [List.map_append, List.map_cons, List.map_nil] at hpre
    rw [Specs.Sinsemilla.hashToPoint_concat] at hpre
    cases hpre0 : Specs.Sinsemilla.hashToPoint G.S A
        ((List.range n).map ms) with
    | none =>
      rw [hpre0] at hpre
      simp at hpre
    | some B₀ =>
      rw [hpre0] at hpre
      replace hpre : Specs.Sinsemilla.step G.S (ms n) B₀ = some B₁ := hpre
      obtain ⟨hlast_xA, hlast_yA⟩ := hchain_piece A hAon hAx hAyA B₀ hpre0
      -- the gate completes the last step
      have hyck' : 4 * last.lambda2 * (last.xA - tailFirst.xA)
          = 2 * DoubleAndAdd.yA last + 2 * enterYA isFinal tailFirst := by
        have h := hyck
        rw [gate_yRhs_enterYA] at h
        simpa only [Gate.yLhs] using h
      have hlast_yA' := hlast_yA
      simp only [DoubleAndAdd.yA, DoubleAndAdd.xR] at hlast_yA'
      have hsec' := hsec
      simp only [DoubleAndAdd.xR] at hsec'
      have hpin := HashPiece.step_coordinates_of_constraints G.S hpre
        (xp := last.xP) (lambda1 := last.lambda1) (lambda2 := last.lambda2)
        (xa' := tailFirst.xA) (YA' := enterYA isFinal tailFirst)
        (by linear_combination HashPiece.double_halved hlast_yp + hlast_yA
          + 2 * last.lambda1 * hlast_xA)
        hlast_xP
        (by linear_combination hlast_yA'
          + 2 * (last.lambda1 + last.lambda2) * hlast_xA)
        (by linear_combination hsec')
        (by linear_combination hyck' - 4 * last.lambda2 * hlast_xA - 2 * hlast_yA)
      have hB₀valid : B₀.Valid :=
        Specs.Sinsemilla.hashToPoint_valid hAvalid
          (fun m hm => by
            rcases List.mem_map.mp hm with ⟨r, hr, rfl⟩
            exact hms r)
          hpre0
      have hB₁valid : B₁.Valid :=
        Specs.Sinsemilla.step_valid hB₀valid (hms n) hpre
      have hB₁0 : B₁ ≠ 0 :=
        Specs.Sinsemilla.step_ne_zero hB₀valid (hms n) hpre
      have hB₁on : B₁.OnCurve := by
        rcases hB₁valid with h | h
        · exact h
        · exact False.elim (hB₁0 h)
      exact htail_chain B₁ hB₁on
        (hpin.1.symm.trans htfxA) hpin.2.symm B hB

theorem soundness (G : Generators) (n : ℕ) (rest : List ℕ)
    (tail : GeneralFormalCircuit.WithHint Fp (Input rest.length) (Output rest))
    (tailLen : ℕ) (htail : ∀ inp, tail.localLength inp = tailLen)
    (hcwg : tail.channelsWithGuarantees = [])
    (hcwr : tail.channelsWithRequirements = [])
    (hS : tail.Spec = Spec G rest)
    (hAss : tail.Assumptions = fun _ _ => True) :
    letI := elaborated G n rest tail tailLen htail hcwg hcwr
    GeneralFormalCircuit.WithHint.Soundness Fp (main G n rest tail)
      (fun _ _ => True) (Spec G (n :: rest)) := by
  circuit_proof_start [HashPiece.circuit, HashPiece.Spec, Gate.circuit, Gate.Spec]
  obtain ⟨h_piece, h_tail, h_gate⟩ := h_holds
  simp only [hAss] at h_tail
  replace h_tail := h_tail trivial
  rw [hS] at h_tail
  simp only [Spec, List.isEmpty_cons,
    show ∀ r : DoubleAndAddRow Fp, enterYA false r = DoubleAndAdd.yA r
      from fun _ => rfl,
    circuit_norm] at h_piece h_tail h_gate ⊢
  obtain ⟨ms, hms, hrecomb, hzs, hlxP, hlyp, hchain⟩ := h_piece
  obtain ⟨htfxA, tailChunks, htailPC, htailZs, htailchain⟩ := h_tail
  obtain ⟨hsec, hyck⟩ := h_gate
  refine ⟨⟨(List.range (n + 1)).map ms ++ tailChunks, ?_, ?_, ?_⟩, Or.inl hcwr⟩
  · -- the pieces decompose into the chunks
    simp only [PieceChunks]
    refine ⟨ms, hms, ?_, tailChunks, rfl, ?_⟩
    · rw [← h_input.1]
      simpa using hrecomb
    · have hv : Vector.tail input.pieces
          = Vector.map (Expression.eval env)
            (Vector.cast (by omega) (Vector.tail input_var.pieces)) := by
        rw [← h_input.1]
        ext i hi
        simp
      rw [hv]
      exact htailPC
  · -- the running-sum vectors
    erw [HVec.eval_cons]
    simp only [ZsFacts, HVec.head_cons]
    refine ⟨?_, ?_⟩
    · rw [CircuitType.eval_var_fields, hzs]
      apply Vector.ext
      intro r hr
      simp only [Vector.getElem_ofFn]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [chunks_head_getD ms tailChunks (r + j) (by simp only [Finset.mem_range] at hj; omega)]
    · rw [chunks_drop_append]
      erw [HVec.tail_cons]
      exact htailZs
  · -- the chain contract
    exact soundness_aux G n rest.isEmpty ms hms hlxP hlyp hchain hsec hyck htfxA
      tailChunks htailchain

theorem completeness (G : Generators) (n : ℕ) (rest : List ℕ)
    (tail : GeneralFormalCircuit.WithHint Fp (Input rest.length) (Output rest))
    (tailLen : ℕ) (htail : ∀ inp, tail.localLength inp = tailLen)
    (hcwg : tail.channelsWithGuarantees = [])
    (hcwr : tail.channelsWithRequirements = [])
    (hPA : tail.ProverAssumptions = ProverAssumptions G rest)
    (hPS : tail.ProverSpec = ProverSpec G rest) :
    letI := elaborated G n rest tail tailLen htail hcwg hcwr
    GeneralFormalCircuit.WithHint.Completeness Fp (main G n rest tail)
      (ProverAssumptions G (n :: rest)) (ProverSpec G (n :: rest)) := by
  circuit_proof_start [HashPiece.circuit, HashPiece.ProverSpec,
    HashPiece.ProverAssumptions, Gate.circuit, Gate.Spec]
  obtain ⟨h_piece_env, h_tail_env⟩ := h_env
  obtain ⟨hbounds, A, B, hAon, hAx, hAy, hchain⟩ := h_assumptions
  have hAvalid : A.Valid := Or.inl hAon
  have hA0 : A ≠ 0 := Point.ne_zero_of_onCurve hAon
  simp only [PieceBounds] at hbounds
  simp only [honestChunks] at hchain
  have hp0 := congrArg
    (fun v : Vector Fp (rest.length + 1) => v[0]) h_input.1
  have hptail := congrArg
    (fun v : Vector Fp (rest.length + 1) => v.tail) h_input.1
  simp only [Vector.getElem_map] at hp0
  try simp only [] at hptail
  have hmt : (Vector.map (Expression.eval env.toEnvironment) input_var.pieces).tail
      = Vector.map (Expression.eval env.toEnvironment)
          (Vector.cast (by omega) (Vector.tail input_var.pieces)) := by
    ext i hi
    simp
  rw [hmt] at hptail
  obtain ⟨B₁, hpre, hsuffix⟩ := Specs.Sinsemilla.hashToPoint_append_some hchain
  have hpre' : Specs.Sinsemilla.hashToPoint G.S A
      ((List.range (n + 1)).map
        (pieceWord (Expression.eval env.toEnvironment input_var.pieces[0])))
      = some B₁ := by
    rw [hp0]
    exact hpre
  have hb1 : ZMod.val (Expression.eval env.toEnvironment input_var.pieces[0])
      < 2 ^ (K * (n + 1)) := by
    rw [hp0]
    exact hbounds.1
  have hPSpiece := h_piece_env ⟨hb1, A, B₁, hAon, hAx, hAy, hpre'⟩
  obtain ⟨-, hsecPS, hzsPS, hchainPS⟩ := hPSpiece
  obtain ⟨hYA0, hBfun⟩ := hchainPS A hA0 hAx hAy
  obtain ⟨hxAsN, hyAcc, hnext⟩ := hBfun B₁ hpre'
  have hB₁0 : B₁ ≠ 0 := by
    apply Specs.Sinsemilla.hashToPoint_ne_zero hAvalid hA0
    · intro m hm
      rcases List.mem_map.mp hm with ⟨r, hr, rfl⟩
      exact HashPiece.pieceWord_lt (Expression.eval env.toEnvironment input_var.pieces[0]) r
    · exact hpre'
  have hB₁valid : B₁.Valid := by
    apply Specs.Sinsemilla.hashToPoint_valid hAvalid
    · intro m hm
      rcases List.mem_map.mp hm with ⟨r, hr, rfl⟩
      exact HashPiece.pieceWord_lt (Expression.eval env.toEnvironment input_var.pieces[0]) r
    · exact hpre'
  have hB₁on : B₁.OnCurve := by
    rcases hB₁valid with h | h
    · exact h
    · exact False.elim (hB₁0 h)
  have hPStail := h_tail_env (by
    rw [hPA]
    refine ⟨?_, B₁, B, hB₁on, hxAsN.symm, hyAcc.symm, ?_⟩
    · erw [hptail]
      exact hbounds.2
    · erw [hptail]
      exact hsuffix)
  rw [hPS] at hPStail
  obtain ⟨-, htfxA, htailZsH, hAfun⟩ := hPStail
  obtain ⟨henter, hBfin⟩ := hAfun B₁ hB₁0 hxAsN.symm hyAcc.symm
  obtain ⟨hpx, hpy⟩ := hBfin B (by erw [hptail]; exact hsuffix)
  dsimp only at htfxA henter hpx hpy
  refine ⟨⟨⟨hb1, A, B₁, hAon, hAx, hAy, hpre'⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- the tail's honest-prover assumptions
    rw [hPA]
    refine ⟨?_, B₁, B, hB₁on, hxAsN.symm, hyAcc.symm, ?_⟩
    · erw [hptail]
      exact hbounds.2
    · erw [hptail]
      exact hsuffix
  · -- the gate's secant equation on honest values
    rw [htfxA]
    linear_combination -hsecPS
  · -- the gate's Y_A check on honest values
    rw [gate_yRhs_enterYA]
    simp only [Gate.yLhs]
    have hnext' := hnext
    simp only [nextYA] at hnext'
    rw [htfxA] at henter ⊢
    linear_combination 2 * hnext' - 2 * henter
  · -- the honest running-sum vectors
    erw [HVec.eval_cons]
    simp only [ZsHonest, HVec.head_cons]
    refine ⟨?_, ?_⟩
    · rw [CircuitType.eval_var_fields, hzsPS]
      congr 1
      funext r
      exact congrArg (fun p => pieceZ p r.val) hp0
    · erw [HVec.tail_cons]
      rw [← hptail]
      exact htailZsH
  · -- the level's chain contract
    intro A' hA'0 hA'x hA'y
    obtain rfl : A' = A := by
      rcases A with ⟨Ax, Ay⟩
      rcases A' with ⟨Ax', Ay'⟩
      simp only [Point.mk.injEq]
      exact ⟨hA'x.trans hAx.symm, hA'y.trans hAy.symm⟩
    refine ⟨hYA0, ?_⟩
    intro Bf hBf
    simp only [honestChunks] at hBf
    rw [hchain] at hBf
    obtain rfl : B = Bf := Option.some.inj hBf
    exact ⟨hpx, hpy⟩

def circuit (G : Generators) (n : ℕ) (rest : List ℕ)
    (tail : GeneralFormalCircuit.WithHint Fp (Input rest.length) (Output rest))
    (tailLen : ℕ) (htail : ∀ inp, tail.localLength inp = tailLen)
    (hcwg : tail.channelsWithGuarantees = [])
    (hcwr : tail.channelsWithRequirements = [])
    (hS : tail.Spec = Spec G rest)
    (hAss : tail.Assumptions = fun _ _ => True)
    (hPA : tail.ProverAssumptions = ProverAssumptions G rest)
    (hPS : tail.ProverSpec = ProverSpec G rest) :
    GeneralFormalCircuit.WithHint Fp (Input (rest.length + 1))
      (Output (n :: rest)) where
  main := main G n rest tail
  elaborated := elaborated G n rest tail tailLen htail hcwg hcwr
  Spec := Spec G (n :: rest)
  ProverAssumptions := ProverAssumptions G (n :: rest)
  ProverSpec := ProverSpec G (n :: rest)
  soundness := soundness G n rest tail tailLen htail hcwg hcwr hS hAss
  completeness := completeness G n rest tail tailLen htail hcwg hcwr hPA hPS
  requirementsChannelsLawful := by
    try dsimp only [main]
    simp only [circuit_norm, seval, hcwr]
    try first | ac_rfl | trivial | tauto

end Cons

/-- The chain tail over the remaining word counts, bundled with the contracts that its
spec fields are the canonical recursive ones, its local length is constant, and it
declares no channels. -/
def circuit (G : Generators) : (ns : List ℕ) →
    { c : GeneralFormalCircuit.WithHint Fp (Input ns.length) (Output ns) //
      c.Spec = Spec G ns ∧ c.Assumptions = (fun _ _ => True) ∧
        c.ProverAssumptions = ProverAssumptions G ns ∧
        c.ProverSpec = ProverSpec G ns ∧
        (∀ inp, c.localLength inp = chainLength ns) ∧
        c.channelsWithGuarantees = [] ∧ c.channelsWithRequirements = [] }
  | [] => ⟨Nil.circuit G, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  | n :: rest =>
    let ⟨tail, hS, hAss, hPA, hPS, hLen, hcwg, hcwr⟩ := circuit G rest
    ⟨Cons.circuit G n rest tail (chainLength rest) hLen hcwg hcwr hS hAss hPA hPS,
      rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩

end Chain

/-!
### The `hash_to_point` entry (`SinsemillaInstructions::hash_to_point`)

Public-point initialization: `x_Q` is constrained to the domain constant, the chain
runs with the accumulator hint `y_Q`, and the `q_sinsemilla4` gate (`Initial y_Q`)
pins the first row's derived `Y_A` to `2·y_Q`. The output exposes the full per-piece
running sums `zs`, mirroring halo2's `(Point, Vec<RunningSum>)` `hash_to_point` output
(`NoteCommit`/`CommitIvk` read individual `zs[i][j]` cells for the canonicity gates).
The `MerkleCRH` path that only needs the `z₁` cells uses the `Z1s` projection below.
-/

namespace HashToPoint

/-- Outputs of `hash_to_point`: the hash point and the full per-piece running sums. -/
structure Output (ns : List ℕ) (F : Type) where
  point : Point F
  zs : HVec (Chain.zLengths ns) F
deriving ProvableStruct

def main (G : Generators) (Q : Point Fp) (n₀ : ℕ) (ns : List ℕ)
    (pieces : Var (fields (ns.length + 1)) Fp) :
    Circuit Fp (Var (Output (n₀ :: ns)) Fp) := do
  let xQ <== Expression.const Q.x
  let out ← (Chain.circuit G (n₀ :: ns)).1
    { pieces := pieces, xA := xQ, yA := fun _ => Q.y }
  InitialYQ.circuit { yQ := Q.y } { doubleAndAdd := out.first }
  return { point := out.point, zs := out.zs }

instance elaborated (G : Generators) (Q : Point Fp) (n₀ : ℕ)
    (ns : List ℕ) :
    ElaboratedCircuit Fp (fields (ns.length + 1)) (Output (n₀ :: ns))
      (main G Q n₀ ns) where
  localLength _ := 1 + Chain.chainLength (n₀ :: ns)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, (Chain.circuit G (n₀ :: ns)).2.2.2.2.2.1,
      InitialYQ.circuit]
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    dsimp only [main]
    simp only [circuit_norm, seval, InitialYQ.circuit,
      (Chain.circuit G (n₀ :: ns)).2.2.2.2.2.2.1]
    try trivial

def Spec (G : Generators) (Q : Point Fp) (n₀ : ℕ) (ns : List ℕ)
    (pieces : Value (fields (ns.length + 1)) Fp)
    (output : Value (Output (n₀ :: ns)) Fp)
    (_ : ProverData Fp) : Prop :=
  ∃ chunks : List ℕ, Chain.PieceChunks (n₀ :: ns) pieces chunks ∧
    Chain.ZsFacts (n₀ :: ns) chunks output.zs ∧
    ∀ B, Specs.Sinsemilla.hashToPoint G.S Q chunks = some B →
      output.point = B

def ProverAssumptions (G : Generators) (Q : Point Fp) (n₀ : ℕ)
    (ns : List ℕ) (pieces : ProverValue (fields (ns.length + 1)) Fp)
    (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  Chain.PieceBounds (n₀ :: ns) pieces ∧
  ∃ B, Specs.Sinsemilla.hashToPoint G.S Q
    (Chain.honestChunks (n₀ :: ns) pieces) = some B

def ProverSpec (G : Generators) (Q : Point Fp) (n₀ : ℕ) (ns : List ℕ)
    (pieces : ProverValue (fields (ns.length + 1)) Fp)
    (output : ProverValue (Output (n₀ :: ns)) Fp)
    (_ : ProverHint Fp) : Prop :=
  Chain.ZsHonest (n₀ :: ns) pieces output.zs ∧
  ∀ B, Specs.Sinsemilla.hashToPoint G.S Q
      (Chain.honestChunks (n₀ :: ns) pieces) = some B →
    output.point = B

theorem soundness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q n₀ ns)
      (fun _ _ => True) (Spec G Q n₀ ns) := by
  circuit_proof_start [InitialYQ.circuit, InitialYQ.Spec]
  obtain ⟨h_xQ, h_chain, h_yQ⟩ := h_holds
  simp only [(Chain.circuit G (n₀ :: ns)).2.2.1] at h_chain
  replace h_chain := h_chain trivial
  rw [(Chain.circuit G (n₀ :: ns)).2.1] at h_chain
  simp only [Chain.Spec] at h_chain
  obtain ⟨hfxA, chunks, hPC, hZs, hchainAll⟩ := h_chain
  refine ⟨⟨chunks, hPC, ?_, ?_⟩, Or.inl (Chain.circuit G (n₀ :: ns)).2.2.2.2.2.2.2⟩
  · convert hZs using 2
  · intro B hB
    obtain ⟨px, py⟩ := hchainAll Q hQ (by rw [h_xQ])
      (by exact h_yQ.symm) B hB
    apply Point.ext_coords
    exact Prod.ext px py

theorem completeness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q n₀ ns)
      (ProverAssumptions G Q n₀ ns) (ProverSpec G Q n₀ ns) := by
  circuit_proof_start [InitialYQ.circuit, InitialYQ.Spec]
  obtain ⟨h_xQ_env, h_chain_env⟩ := h_env
  obtain ⟨hbounds, B, hchain⟩ := h_assumptions
  have hPSchain := h_chain_env (by
    rw [(Chain.circuit G (n₀ :: ns)).2.2.2.1]
    exact ⟨hbounds, Q, B, hQ, h_xQ_env.symm, rfl, hchain⟩)
  rw [(Chain.circuit G (n₀ :: ns)).2.2.2.2.1] at hPSchain
  obtain ⟨-, htfxA, hZsH, hAfun⟩ := hPSchain
  obtain ⟨henter, hBfin⟩ := hAfun Q (Point.ne_zero_of_onCurve hQ) h_xQ_env.symm rfl
  obtain ⟨px, py⟩ := hBfin B hchain
  refine ⟨⟨h_xQ_env, ?_, ?_⟩, ?_, ?_⟩
  · rw [(Chain.circuit G (n₀ :: ns)).2.2.2.1]
    exact ⟨hbounds, Q, B, hQ, h_xQ_env.symm, rfl, hchain⟩
  · exact henter
  · convert hZsH using 2
  · intro B' hB'
    rw [hchain] at hB'
    obtain rfl : B = B' := Option.some.inj hB'
    apply Point.ext_coords
    exact Prod.ext px py

/--
WARNING: this source-shaped `hash_to_point` entry is intentionally restricted to
nonempty messages (`n₀ :: ns`).

The halo2 source API accepts an arbitrary `Vec<MessagePiece>`, including the empty
vector. That empty-message path is not sound for the semantic spec we want here:
after public `Q` initialization, no piece row is emitted, so no Sinsemilla chaining
gate ties the final dummy `y_a` cell to the initialized `Q.y`. The `Initial y_Q` gate
constrains the entering double-and-add expression, but in the empty case the output
`y` is the dummy row's `lambda1`; without a piece boundary gate, constraints do not
force that cell to equal `Q.y`.

So this is a deliberate source non-conformance. The internal `Chain.Nil` circuit
models the empty tail needed by nonempty messages, not a standalone empty
`hash_to_point` entry.
-/
def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint Fp (fields (ns.length + 1))
      (Output (n₀ :: ns)) where
  main := main G Q n₀ ns
  elaborated := elaborated G Q n₀ ns
  Spec := Spec G Q n₀ ns
  ProverAssumptions := ProverAssumptions G Q n₀ ns
  ProverSpec := ProverSpec G Q n₀ ns
  soundness := soundness G Q hQ n₀ ns
  completeness := completeness G Q hQ n₀ ns
  requirementsChannelsLawful := by
    try dsimp only [main]
    simp only [circuit_norm, seval, InitialYQ.circuit, (Chain.circuit G (n₀ :: ns)).2.2.2.2.2.2.2]

/-! ### `Z1s`: the `z₁`-only `hash_to_point` view (`MerkleCRH` path)

`MerkleCRH` reads only each piece's `z₁` running-sum cell. This is the `z₁`-projecting
view of `hash_to_point`: `z1s[i] = zs[i][1]` via `Chain.z1sOfZs`, so the single source of truth is
`hash_to_point`'s running sums `zs`. The output is exposed through the named `output`
definition, so parents (Merkle) see an opaque `Z1s.output …` reasoned about via the
`Spec`, rather than the `Chain.z1sOfZs` projection internals. -/
namespace Z1s

/-- Outputs of the `z₁`-only `hash_to_point` view: the hash point and each piece's `z₁`
running-sum cell. -/
structure Output (ns : List ℕ) (F : Type) where
  point : Point F
  z1s : Vector F ns.length

instance (ns : List ℕ) : ProvableStruct (Output ns) where
  components := [Point, fields ns.length]
  toComponents := fun { point, z1s } => .cons point (.cons z1s .nil)
  fromComponents := fun (.cons point (.cons z1s .nil)) => { point, z1s }

/-- Hand-written analogue of the `deriving ProvableStruct` handler's generated
`fromComponents_cons` simp lemma (the instance above is hand-written, so none is
generated): lets `simp` reduce `fromComponents` applications without going through the
private match auxiliary, which no longer reduces at reducible transparency (4.30 bump). -/
@[circuit_norm]
theorem Output.fromComponents_cons (ns : List ℕ) {F : Type}
    (point : Point F) (z1s : Vector F ns.length) :
    fromComponents (α := Output ns) (F := F)
      (.cons point (.cons z1s .nil)) = { point, z1s } := rfl

def main (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (n₀ : ℕ) (ns : List ℕ)
    (pieces : Var (fields (ns.length + 1)) Fp) :
    Circuit Fp (Var (Output (n₀ :: ns)) Fp) := do
  let out ← circuit G Q hQ n₀ ns pieces
  return { point := out.point, z1s := Chain.z1sOfZs (n₀ :: ns) out.zs }

/-- The output cells of `Z1s`, kept as a named (opaque) definition so parent circuits
reason about `Z1s.output …` via the `Spec` instead of unfolding the `Chain.z1sOfZs`
projection. It is exactly the output `elaborate_circuit` derives for `main`, so `output_eq`
is definitional. -/
def output (G : Generators) (Q : Point Fp) (n₀ : ℕ) (ns : List ℕ)
    (input : Var (fields (ns.length + 1)) Fp) (offset : ℕ) : Var (Output (n₀ :: ns)) Fp :=
  let e := (HashToPoint.main G Q n₀ ns input).output offset
  { point := e.point, z1s := Chain.z1sOfZs (n₀ :: ns) e.zs }

instance elaborated (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (n₀ : ℕ) (ns : List ℕ) :
    ElaboratedCircuit Fp (fields (ns.length + 1)) (Output (n₀ :: ns))
      (main G Q hQ n₀ ns) := by
  elaborate_circuit_with {
    output input offset := output G Q n₀ ns input offset
  }

def Spec (G : Generators) (Q : Point Fp) (n₀ : ℕ) (ns : List ℕ)
    (pieces : Value (fields (ns.length + 1)) Fp)
    (output : Value (Output (n₀ :: ns)) Fp)
    (_ : ProverData Fp) : Prop :=
  ∃ chunks : List ℕ, Chain.PieceChunks (n₀ :: ns) pieces chunks ∧
    Chain.Z1Facts (n₀ :: ns) chunks output.z1s ∧
    ∀ B, Specs.Sinsemilla.hashToPoint G.S Q chunks = some B →
      output.point = B

def ProverAssumptions (G : Generators) (Q : Point Fp) (n₀ : ℕ)
    (ns : List ℕ) (pieces : ProverValue (fields (ns.length + 1)) Fp)
    (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  Chain.PieceBounds (n₀ :: ns) pieces ∧
  ∃ B, Specs.Sinsemilla.hashToPoint G.S Q
    (Chain.honestChunks (n₀ :: ns) pieces) = some B

def ProverSpec (G : Generators) (Q : Point Fp) (n₀ : ℕ) (ns : List ℕ)
    (pieces : ProverValue (fields (ns.length + 1)) Fp)
    (output : ProverValue (Output (n₀ :: ns)) Fp)
    (_ : ProverHint Fp) : Prop :=
  Chain.Z1sHonest (n₀ :: ns) pieces output.z1s ∧
  ∀ B, Specs.Sinsemilla.hashToPoint G.S Q
      (Chain.honestChunks (n₀ :: ns) pieces) = some B →
    output.point = B

theorem soundness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ n₀ ns)
      (fun _ _ => True) (Spec G Q n₀ ns) := by
  circuit_proof_start [output, HashToPoint.circuit, HashToPoint.Spec]
  obtain ⟨chunks, hPC, hZs, hfun⟩ := h_holds
  refine ⟨chunks, hPC, ?_, ?_⟩
  · rw [← ProvableType.eval_fields, Chain.eval_z1sOfZs]
    exact Chain.z1Facts_of_zsFacts _ chunks _ hZs
  · intro B hB
    exact hfun B hB

theorem completeness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ n₀ ns)
      (ProverAssumptions G Q n₀ ns) (ProverSpec G Q n₀ ns) := by
  circuit_proof_start [output, HashToPoint.circuit,
    HashToPoint.ProverAssumptions, HashToPoint.ProverSpec]
  obtain ⟨-, hZsH, hAfun⟩ := h_env h_assumptions
  refine ⟨h_assumptions, ?_, ?_⟩
  · rw [← ProvableType.eval_fields, Chain.eval_z1sOfZs]
    exact Chain.z1sHonest_of_zsHonest _ _ _ h_assumptions.1 hZsH
  · intro B' hB'
    exact hAfun B' hB'

def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (n₀ : ℕ) (ns : List ℕ) :
    GeneralFormalCircuit.WithHint Fp (fields (ns.length + 1))
      (Output (n₀ :: ns)) where
  main := main G Q hQ n₀ ns
  elaborated := elaborated G Q hQ n₀ ns
  Spec := Spec G Q n₀ ns
  ProverAssumptions := ProverAssumptions G Q n₀ ns
  ProverSpec := ProverSpec G Q n₀ ns
  soundness := soundness G Q hQ n₀ ns
  completeness := completeness G Q hQ n₀ ns

end Z1s

end HashToPoint

end Orchard.Sinsemilla
