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

private theorem two_ne_zero_Fp : (2 : Ecc.Fp) ≠ 0 := by
  rw [show (2 : Ecc.Fp) = ((2 : ℕ) : Ecc.Fp) by norm_num, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD] at this

private theorem double_halved {f g s : Ecc.Fp} (h : f * (2 : Ecc.Fp)⁻¹ - g = s) :
    f - 2 * g = 2 * s := by
  have h2 := congrArg (fun t => 2 * t) h
  simp only [mul_sub] at h2
  rw [show (2 : Ecc.Fp) * (f * (2 : Ecc.Fp)⁻¹) = f from by
    rw [mul_comm f, ← mul_assoc, mul_inv_cancel₀ two_ne_zero_Fp, one_mul]] at h2
  linear_combination h2

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
    {xp lambda1 lambda2 xa' YA' : Ecc.Fp}
    (hYP : 2 * A.y - 2 * lambda1 * (A.x - xp) = 2 * (S m).y)
    (hXP : xp = (S m).x)
    (hYA : 2 * A.y = (lambda1 + lambda2) * (A.x - (lambda1 * lambda1 - A.x - xp)))
    (hSecant : lambda2 * lambda2 = xa' + (lambda1 * lambda1 - A.x - xp) + A.x)
    (hYCheck : 4 * lambda2 * (A.x - xa') = 4 * A.y + 2 * YA') :
    xa' = B.x ∧ YA' = 2 * B.y := by
  have hYP' : A.y - lambda1 * (A.x - xp) = (S m).y :=
    mul_left_cancel₀ two_ne_zero_Fp (by linear_combination hYP)
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
    linear_combination -hYP'
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
  · apply mul_left_cancel₀ two_ne_zero_Fp
    rw [← hBy, ← hl2, show lambda2 * lambda2 - A.x - R.x = xa' by
      linear_combination hSecant + hxR]
    linear_combination -hYCheck

/-- Telescoped base-`2^K` running sum (mirrors the short-mul chain lemma). -/
private theorem chain_eq_sum {n : ℕ} (z : ℕ → Ecc.Fp) (ms : ℕ → ℕ)
    (hword : ∀ r < n, z r = (ms r : Ecc.Fp) + 2 ^ K * z (r + 1))
    (hzn : z n = 0) :
    z 0 = ((∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) : Ecc.Fp) := by
  have key : ∀ r ≤ n,
      z 0 = ((∑ j ∈ Finset.range r, ms j * 2 ^ (K * j) : ℕ) : Ecc.Fp)
        + z r * ((2 ^ (K * r) : ℕ) : Ecc.Fp) := by
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

/-- The verifier-side contract of one piece, see `step_pinned` for the chain step. The
chain runs through the first `w` words; the last word's lookup facts are exposed so the
composing circuit can finish the step with its boundary gate. -/
def Spec (G : Generators) (w : ℕ) (input : Value Input Ecc.Fp)
    (output : Value Output Ecc.Fp) (_ : ProverData Ecc.Fp) : Prop :=
  ∃ ms : ℕ → ℕ,
    (∀ r, ms r < 2 ^ K) ∧
    input.piece = ((∑ r ∈ Finset.range (w + 1), ms r * 2 ^ (K * r) : ℕ) : Ecc.Fp) ∧
    output.first.xA = input.xA ∧
    output.last.xP = (G.S (ms w)).x ∧
    DoubleAndAdd.yA output.last * (2 : Ecc.Fp)⁻¹
        - output.last.lambda1 * (output.last.xA - output.last.xP) = (G.S (ms w)).y ∧
    ∀ A : SWPoint Pallas.curve, A ≠ 0 → A.x = input.xA →
      2 * A.y = DoubleAndAdd.yA output.first →
      ∀ B, Orchard.Specs.Sinsemilla.hashToPoint G.S A
          ((List.range w).map ms) = some B →
        output.last.xA = B.x ∧ 2 * B.y = DoubleAndAdd.yA output.last

/--
The chain induction of one piece over cleaned row facts: `dR r` are the per-row cell
values, `zV r` the running sum values. Splitting this from `soundness` keeps each
declaration within the elaboration budget.
-/
private theorem soundness_aux (G : Generators) (w : ℕ)
    (dR : ℕ → DoubleAndAddRow Ecc.Fp) (zV : ℕ → Ecc.Fp) (piece xA : Ecc.Fp)
    (hxA0 : (dR 0).xA = xA)
    (hz0 : zV 0 = piece)
    (hL : ∀ r, r < w + 1 → ∃ m : ℕ, m < 2 ^ K ∧
      (if r = w then zV r else zV r - 2 ^ K * zV (r + 1)) = (m : Ecc.Fp) ∧
      (dR r).xP = (G.S m).x ∧
      DoubleAndAdd.yA (dR r) * (2 : Ecc.Fp)⁻¹
        - (dR r).lambda1 * ((dR r).xA - (dR r).xP) = (G.S m).y)
    (hG : ∀ r, r < w →
      ((dR r).lambda2 * (dR r).lambda2
        = (dR (r + 1)).xA + ((dR r).lambda1 * (dR r).lambda1 - (dR r).xA - (dR r).xP)
          + (dR r).xA) ∧
      4 * (dR r).lambda2 * ((dR r).xA - (dR (r + 1)).xA)
        = 2 * DoubleAndAdd.yA (dR r) + 2 * DoubleAndAdd.yA (dR (r + 1))) :
    ∃ ms : ℕ → ℕ,
      (∀ r, ms r < 2 ^ K) ∧
      piece = ((∑ r ∈ Finset.range (w + 1), ms r * 2 ^ (K * r) : ℕ) : Ecc.Fp) ∧
      (dR 0).xA = xA ∧
      (dR w).xP = (G.S (ms w)).x ∧
      DoubleAndAdd.yA (dR w) * (2 : Ecc.Fp)⁻¹
        - (dR w).lambda1 * ((dR w).xA - (dR w).xP) = (G.S (ms w)).y ∧
      ∀ A : SWPoint Pallas.curve, A ≠ 0 → A.x = xA →
        2 * A.y = DoubleAndAdd.yA (dR 0) →
        ∀ B, Orchard.Specs.Sinsemilla.hashToPoint G.S A
            ((List.range w).map ms) = some B →
          (dR w).xA = B.x ∧ 2 * B.y = DoubleAndAdd.yA (dR w) := by
  -- choose the word values
  have hLE : ∀ r : Fin (w + 1), ∃ m : ℕ, m < 2 ^ K ∧
      (if r.val = w then zV r.val else zV r.val - 2 ^ K * zV (r.val + 1)) = (m : Ecc.Fp) ∧
      (dR r.val).xP = (G.S m).x ∧
      DoubleAndAdd.yA (dR r.val) * (2 : Ecc.Fp)⁻¹
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
      = ((∑ r ∈ Finset.range (w + 1), ms r * 2 ^ (K * r) : ℕ) : Ecc.Fp) := by
    rw [← hz0]
    have key : ∀ r, r ≤ w →
        zV 0 = ((∑ j ∈ Finset.range r, ms j * 2 ^ (K * j) : ℕ) : Ecc.Fp)
          + zV r * ((2 ^ (K * r) : ℕ) : Ecc.Fp) := by
      intro r hr
      induction r with
      | zero => simp
      | succ v ih =>
        have h := hmf_word ⟨v, by omega⟩
        rw [if_neg (show ¬ (⟨v, by omega⟩ : Fin (w + 1)).val = w by
          simp only [Fin.val_mk]; omega)] at h
        rw [ih (by omega), Finset.sum_range_succ]
        rw [← hms_at v (by omega)] at h
        push_cast
        rw [show K * (v + 1) = K * v + K by ring]
        push_cast [pow_add]
        linear_combination ((2 : Ecc.Fp) ^ (K * v)) * h
    have hlast : zV w = ((ms w : ℕ) : Ecc.Fp) := by
      have h := hmf_word ⟨w, by omega⟩
      rw [if_pos rfl] at h
      rw [hms_at w (by omega)]
      exact h
    rw [key w (by omega), hlast, Finset.sum_range_succ]
    push_cast
    ring
  refine ⟨ms, hms_lt, hpiece, hxA0, ?_, ?_, ?_⟩
  · rw [hms_at w (by omega)]
    exact hmf_x ⟨w, by omega⟩
  · rw [hms_at w (by omega)]
    exact hmf_y ⟨w, by omega⟩
  -- the chain invariant over message prefixes
  intro A hA0 hAx hAyA B hchain
  have hinv : ∀ r, r ≤ w → ∀ Ar : SWPoint Pallas.curve,
      Orchard.Specs.Sinsemilla.hashToPoint G.S A ((List.range r).map ms) = some Ar →
      (dR r).xA = Ar.x ∧ 2 * Ar.y = DoubleAndAdd.yA (dR r) := by
    intro r
    induction r with
    | zero =>
      intro _ Ar hAr
      rw [show ((List.range 0).map ms) = ([] : List ℕ) from rfl,
        Orchard.Specs.Sinsemilla.hashToPoint_nil] at hAr
      obtain rfl : A = Ar := Option.some.inj hAr
      exact ⟨hxA0.trans hAx.symm, hAyA⟩
    | succ r ih =>
      intro hr Ar hAr
      rw [List.range_succ] at hAr
      simp only [List.map_append, List.map_cons, List.map_nil] at hAr
      rw [Orchard.Specs.Sinsemilla.hashToPoint_concat] at hAr
      cases hpre : Orchard.Specs.Sinsemilla.hashToPoint G.S A ((List.range r).map ms) with
      | none =>
        rw [hpre] at hAr
        simp at hAr
      | some Ap =>
        rw [hpre] at hAr
        replace hAr : Orchard.Specs.Sinsemilla.step G.S Ap (ms r) = some Ar := hAr
        obtain ⟨hxAr, hyAr⟩ := ih (by omega) Ap hpre
        have hxw := hmf_x ⟨r, by omega⟩
        have hyw := hmf_y ⟨r, by omega⟩
        rw [← hms_at r (by omega)] at hxw hyw
        obtain ⟨hsec, hyck⟩ := hG r (by omega)
        have hyAr' := hyAr
        simp only [DoubleAndAdd.yA, DoubleAndAdd.xR] at hyAr'
        have hyw2 := double_halved hyw
        have hpin := step_pinned G.S hAr
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


end HashPiece

end Orchard.Sinsemilla
