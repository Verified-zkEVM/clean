import Clean.Orchard.Sinsemilla
import Clean.Orchard.Specs.Sinsemilla
import Clean.Orchard.Ecc.AddIncomplete

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
open Orchard.Specs.Sinsemilla (K Generators)

/-- One row of the Sinsemilla generator table:
`(table_idx, table_x, table_y)`. -/
structure GeneratorTableRow (F : Type) where
  idx : F
  x : F
  y : F
deriving ProvableStruct

/-- The `2^K`-entry generator lookup table `(j, S(j).x, S(j).y)`. -/
def generatorTable (G : Generators) : Table Ecc.Fp GeneratorTableRow := .fromStatic {
  name := "sinsemilla generators"
  length := 2 ^ K
  row i := { idx := (i.val : Ecc.Fp), x := (G.S i.val).x, y := (G.S i.val).y }
  index r := r.idx.val
  Spec r := ∃ m : ℕ, m < 2 ^ K ∧
    r.idx = (m : Ecc.Fp) ∧ r.x = (G.S m).x ∧ r.y = (G.S m).y
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
def pieceWord (p : Ecc.Fp) (r : ℕ) : ℕ := p.val / 2 ^ (K * r) % 2 ^ K

/-- The honest running sum value `z_r = ⌊piece / 2^(K·r)⌋`. -/
def pieceZ (p : Ecc.Fp) (r : ℕ) : Ecc.Fp := ((p.val / 2 ^ (K * r) : ℕ) : Ecc.Fp)

/-- Honest cell values of one double-and-add row, computed from the entering
accumulator `(x_a, y_a)` and the generator `(x_p, y_p)`
(`hash_to_point.rs::hash_piece` assignment formulas; total via `0⁻¹ = 0`). -/
def rowValue (acc : Ecc.Fp × Ecc.Fp) (gen : Ecc.Fp × Ecc.Fp) :
    Ecc.Fp × Ecc.Fp × (Ecc.Fp × Ecc.Fp) :=
  let lambda1 := (acc.2 - gen.2) * (acc.1 - gen.1)⁻¹
  let xR := lambda1 * lambda1 - acc.1 - gen.1
  let lambda2 := 2 * acc.2 * (acc.1 - xR)⁻¹ - lambda1
  let xANext := lambda2 * lambda2 - acc.1 - xR
  let yANext := lambda2 * (acc.1 - xANext) - acc.2
  (lambda1, lambda2, (xANext, yANext))

/-- The honest accumulator after `r` words of a piece. -/
def accAfter (G : Generators) (acc : Ecc.Fp × Ecc.Fp) (p : Ecc.Fp) : ℕ → Ecc.Fp × Ecc.Fp
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
  yA : UnconstrainedDep field F
deriving CircuitType

/-- Outputs of one piece: its first and last gate rows (the composing circuit emits
the gates linking pieces), the exit `x_A` cell, and the exit accumulator
`y`-coordinate hint. -/
structure Output (F : Type) where
  first : DoubleAndAddRow F
  last : DoubleAndAddRow F
  xANext : F
  yANext : UnconstrainedDep field F
deriving CircuitType

instance : Inhabited (Var Input Ecc.Fp) :=
  ⟨{ piece := default, xA := default, yA := fun _ => default }⟩

/-- `hash_piece` for `w + 1` words. -/
def main (G : Generators) (w : ℕ) (input : Var Input Ecc.Fp) :
    Circuit Ecc.Fp (Var Output Ecc.Fp) := do
  -- running sum: z_0 is a copy of the piece, z_1 .. z_w are witnessed
  let z₀ <== input.piece
  let zRest ← witnessVector w fun env =>
    .ofFn fun (i : Fin w) => pieceZ (env input.piece) (i.val + 1)
  let zs : Vector (Expression Ecc.Fp) (w + 1) :=
    Vector.cast (Nat.add_comm 1 w) ((#v[z₀] : Vector (Expression Ecc.Fp) 1) ++ zRest)
  -- row cells: x_p, λ₁, λ₂ per word, and the next-row x_a per word
  let xPs ← witnessVector (w + 1) fun env =>
    .ofFn fun (i : Fin (w + 1)) => (G.S (pieceWord (env input.piece) i.val)).x
  let l1s ← witnessVector (w + 1) fun env =>
    .ofFn fun (i : Fin (w + 1)) =>
      (rowValue (accAfter G (env input.xA, input.yA env) (env input.piece) i.val)
        ((G.S (pieceWord (env input.piece) i.val)).x,
          (G.S (pieceWord (env input.piece) i.val)).y)).1
  let l2s ← witnessVector (w + 1) fun env =>
    .ofFn fun (i : Fin (w + 1)) =>
      (rowValue (accAfter G (env input.xA, input.yA env) (env input.piece) i.val)
        ((G.S (pieceWord (env input.piece) i.val)).x,
          (G.S (pieceWord (env input.piece) i.val)).y)).2.1
  let xAs ← witnessVector (w + 1) fun env =>
    .ofFn fun (i : Fin (w + 1)) =>
      (accAfter G (env input.xA, input.yA env) (env input.piece) (i.val + 1)).1
  -- the double-and-add row structs (x_a chained from the input cell)
  let dRows : Vector (Var DoubleAndAddRow Ecc.Fp) (w + 1) := .ofFn fun i =>
    { xA := if _ : i.val = 0 then input.xA else xAs[i.val - 1]'(by omega),
      xP := xPs[i.val]'(i.isLt),
      lambda1 := l1s[i.val]'(i.isLt),
      lambda2 := l2s[i.val]'(i.isLt) }
  -- per-row generator lookups: the word is `z_r - 2^K·z_{r+1}` (with `z_{w+1} = 0`
  -- implicit on the last row), and `y_p` is derived from the row
  let lookupRows : Vector (Var GeneratorTableRow Ecc.Fp) (w + 1) := .ofFn fun i =>
    let row := dRows[i.val]'(i.isLt)
    let word : Expression Ecc.Fp :=
      if h : i.val = w then zs[i.val]'(by omega) else
        zs[i.val]'(by omega) - (2 ^ K : Ecc.Fp) * zs[i.val + 1]'(by omega)
    { idx := word,
      x := row.xP,
      y := DoubleAndAdd.yA row * ((2 : Ecc.Fp)⁻¹ : Ecc.Fp) -
        row.lambda1 * (row.xA - row.xP) }
  Circuit.forEach lookupRows (lookup (generatorTable G))
  -- in-piece gates (`q_s2 = 1` rows): adjacent row pairs
  let gatePairs : Vector (Var Gate.Row Ecc.Fp) w := .ofFn fun i =>
    { cur := dRows[i.val]'(by omega), next := dRows[i.val + 1]'(by omega) }
  Circuit.forEach gatePairs (Gate.circuit { qS2 := 1 })
  return {
    first := dRows[0]'(by omega),
    last := dRows[w]'(by omega),
    xANext := xAs[w]'(by omega),
    yANext := fun env =>
      (accAfter G (env input.xA, input.yA env) (env input.piece) (w + 1)).2 }

instance elaborated (G : Generators) (w : ℕ) :
    ElaboratedCircuit Ecc.Fp Input Output (main G w) := by
  elaborate_circuit

/--
The workhorse of one Sinsemilla row, following the constraint program of the halo2 book
("Sinsemilla / Constraint program"): for a non-degenerate step `(A ⸭ S) ⸭ A = B`, the
row equations pin every cell, where `ya`/`ya'` denote the halves of the derived
`Y_A`-expressions of the current and next row.

Hypotheses are exactly the row constraints:
- `hYP, hXP`: the lookup, with the derived `y_p` and the generator coordinates,
- `hYA`: the current accumulator `y` matches the row's `Y_A` expression (the inductive
  invariant; definitional at initialization and re-established by `hYCheck`),
- `hSecant, hYCheck`: the Sinsemilla gate.
-/
theorem step_pinned (S : ℕ → SWPoint Pallas.curve) {A B : SWPoint Pallas.curve} {m : ℕ}
    (hstep : Orchard.Specs.Sinsemilla.step S A m = some B)
    {xp lambda1 lambda2 xa' ya' : Ecc.Fp}
    (hYP : A.y - lambda1 * (A.x - xp) = (S m).y)
    (hXP : xp = (S m).x)
    (hYA : 2 * A.y = (lambda1 + lambda2) * (A.x - (lambda1 * lambda1 - A.x - xp)))
    (hSecant : lambda2 * lambda2 = xa' + (lambda1 * lambda1 - A.x - xp) + A.x)
    (hYCheck : lambda2 * (A.x - xa') = A.y + ya') :
    xa' = B.x ∧ ya' = B.y := by
  open Orchard.Specs.Sinsemilla in
  -- unfold the spec-level step into its two incomplete additions
  unfold Orchard.Specs.Sinsemilla.step at hstep
  by_cases hc₁ : A = 0 ∨ S m = 0 ∨ A.x = (S m).x
  · rw [Orchard.Specs.Sinsemilla.incompleteAdd, if_pos hc₁] at hstep
    simp at hstep
  rw [Orchard.Specs.Sinsemilla.incompleteAdd, if_neg hc₁] at hstep
  push_neg at hc₁
  obtain ⟨hA0, hS0, hAxS⟩ := hc₁
  set R : SWPoint Pallas.curve := A + S m with hR_def
  rw [show ((some R).bind fun t => Orchard.Specs.Sinsemilla.incompleteAdd t A)
    = Orchard.Specs.Sinsemilla.incompleteAdd R A from rfl] at hstep
  by_cases hc₂ : R = 0 ∨ A = 0 ∨ R.x = A.x
  · rw [Orchard.Specs.Sinsemilla.incompleteAdd, if_pos hc₂] at hstep
    simp at hstep
  rw [Orchard.Specs.Sinsemilla.incompleteAdd, if_neg hc₂] at hstep
  push_neg at hc₂
  obtain ⟨hR0, -, hRxA⟩ := hc₂
  have hB : B = A + R := by
    have := Option.some.inj hstep
    rw [← this, _root_.add_comm]
  subst hXP
  -- nonzero points have nonzero coordinate encodings
  have point_ne_zero : ∀ {P : SWPoint Pallas.curve}, P ≠ 0 →
      ({ x := P.x, y := P.y } : Ecc.Point Ecc.Fp) ≠ Ecc.Point.zero := by
    intro P hP h
    apply hP
    apply SWPoint.ext_pair
    have hx := congrArg Ecc.Point.x h
    have hy := congrArg Ecc.Point.y h
    simp only [Ecc.Point.zero] at hx hy
    rw [show ((0 : SWPoint Pallas.curve).x, (0 : SWPoint Pallas.curve).y)
      = ((0 : Ecc.Fp), (0 : Ecc.Fp)) from rfl, hx, hy]
  -- the first addition: `R = A ⸭ S(m)`, with the chord through `A` and `S(m)`
  have hRadd := Ecc.AddIncomplete.outputValue_eq_add
    (input := { p := { x := A.x, y := A.y }, q := { x := (S m).x, y := (S m).y } })
    (point_ne_zero hA0) (point_ne_zero hS0) hAxS
  rw [show (({ x := A.x, y := A.y } : Ecc.Point Ecc.Fp)).coords = (A.x, A.y) from rfl,
    show (({ x := (S m).x, y := (S m).y } : Ecc.Point Ecc.Fp)).coords
      = ((S m).x, (S m).y) from rfl,
    Pallas.add_coords, ← hR_def] at hRadd
  set slope₁ : Ecc.Fp := ((S m).y - A.y) * ((S m).x - A.x)⁻¹ with hslope₁
  have hRx : slope₁ * slope₁ - A.x - (S m).x = R.x := by
    have := congrArg Prod.fst hRadd
    simpa [Ecc.AddIncomplete.outputValue] using this
  have hRy : slope₁ * (A.x - (slope₁ * slope₁ - A.x - (S m).x)) - A.y = R.y := by
    have := congrArg Prod.snd hRadd
    simpa [Ecc.AddIncomplete.outputValue] using this
  -- the lookup pins `λ₁` to the chord slope
  have hAxS' : A.x - (S m).x ≠ 0 := sub_ne_zero.mpr hAxS
  have hl1 : lambda1 = slope₁ := by
    apply mul_right_cancel₀ hAxS'
    rw [hslope₁, mul_assoc,
      show ((S m).x - A.x)⁻¹ * (A.x - (S m).x) = -1 from by
        rw [show A.x - (S m).x = -((S m).x - A.x) by ring, mul_neg,
          inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hAxS))]]
    linear_combination -hYP
  -- hence `x_R` and the intermediate `y` are the real intermediate point
  have hxR : lambda1 * lambda1 - A.x - (S m).x = R.x := by
    rw [hl1]
    exact hRx
  have hyR : lambda1 * (A.x - R.x) - A.y = R.y := by
    rw [hl1, ← hRx]
    exact hRy
  -- the second addition: `B = A ⸭ R`, with the chord through `A` and `R`
  have hRxA' : A.x - R.x ≠ 0 := sub_ne_zero.mpr fun h => hRxA h.symm
  have hBadd := Ecc.AddIncomplete.outputValue_eq_add
    (input := { p := { x := A.x, y := A.y }, q := { x := R.x, y := R.y } })
    (point_ne_zero hA0) (point_ne_zero hR0) (fun h => hRxA h.symm)
  rw [show (({ x := A.x, y := A.y } : Ecc.Point Ecc.Fp)).coords = (A.x, A.y) from rfl,
    show (({ x := R.x, y := R.y } : Ecc.Point Ecc.Fp)).coords = (R.x, R.y) from rfl,
    Pallas.add_coords, ← hB] at hBadd
  set slope₂ : Ecc.Fp := (R.y - A.y) * (R.x - A.x)⁻¹ with hslope₂
  have hBx : slope₂ * slope₂ - A.x - R.x = B.x := by
    have := congrArg Prod.fst hBadd
    simpa [Ecc.AddIncomplete.outputValue] using this
  have hBy : slope₂ * (A.x - (slope₂ * slope₂ - A.x - R.x)) - A.y = B.y := by
    have := congrArg Prod.snd hBadd
    simpa [Ecc.AddIncomplete.outputValue] using this
  -- the `Y_A` invariant pins `λ₂` to the second chord slope
  have hl2 : lambda2 = slope₂ := by
    apply mul_right_cancel₀ hRxA'
    have hslope₂_mul : slope₂ * (A.x - R.x) = A.y - R.y := by
      rw [hslope₂, mul_assoc,
        show (R.x - A.x)⁻¹ * (A.x - R.x) = -1 from by
          rw [show A.x - R.x = -(R.x - A.x) by ring, mul_neg,
            inv_mul_cancel₀ (sub_ne_zero.mpr hRxA)]]
      ring
    rw [hslope₂_mul]
    have hYA' : 2 * A.y = (lambda1 + lambda2) * (A.x - R.x) := by
      rw [← hxR]
      exact hYA
    linear_combination -hYA' - hyR
  -- the gate then pins the next accumulator to `B`
  constructor
  · rw [← hBx, ← hl2]
    linear_combination -hSecant - hxR
  · rw [← hBy, ← hl2, show lambda2 * lambda2 - A.x - R.x = xa' by
      linear_combination hSecant + hxR]
    linear_combination -hYCheck

end HashPiece

end Orchard.Sinsemilla
