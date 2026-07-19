import Clean.Ironwood.Sinsemilla.ChainTheorems
import Clean.Halo2
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Specs.Sinsemilla
import Clean.Ironwood.Ecc.DoubleAndAdd
import Clean.Ironwood.Ecc.Basic

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/`
- `chip/generator_table.rs` — the `GeneratorTableConfig` (columns `table_idx`, `table_x`,
  `table_y`), the `load()` that fills them with the `2^K` Sinsemilla generators, and the
  3-tuple lookup registration.
- `primitives.rs` — `K = 10`, `C = 253`, the spec-level `hash_to_point` fold
  `Acc ← (Acc ⸭ S(mᵢ)) ⸭ Acc`.

Orchard `feat/ironwood` uses **vanilla** halo2_gadgets 0.5.0 Sinsemilla unchanged (same
gates, same generator table, same `K = 10`, Pallas) — so this port targets the vanilla
chip. The action circuit instantiates it via `SinsemillaChip::load` in
`orchard/src/circuit.rs`.

## Slice-1 scope (this file)

The generator table and the *pure value-level algebra* of one hash piece. Both are lifted
essentially verbatim from the phase-one donor `Clean/Orchard/Sinsemilla/`:

- `generatorTable.rs`: the donor `Halo2.Ironwood.Sinsemilla.generatorTable` is a
  `Table Fp GeneratorTableRow` built on the OLD Clean `Table`/`.fromStatic` abstraction,
  which Halo2-Clean does **not** have. Halo2-Clean tables are raw `loadTable` ops on
  single `TableColumn`s. **Multi-column-table resolution** (the anticipated framework
  question): the S table is three columns of *equal length* `2^K` — real halo2 loads them
  in one `assign_table` closure but as three separate column fills, and errors on uneven
  lengths (`table_layouter.rs:138-146`, `UnevenColumnLengths`). Halo2-Clean's per-column
  `loadTable` already models exactly one such column (dense block `[0, len)` + row-0
  default-fill). So the faithful port is **three `loadTable` ops** (idx, x, y) plus a
  combined `GeneratorTableLoaded` predicate that bundles the three per-column contents at
  a *shared* row — no new multi-column op is warranted. (This mirrors
  `LookupRangeCheck.TableLoaded`, generalized to three columns.)

- The piece algebra (`pieceWord`, `pieceZ`, `rowValue`, `accAfter`, `nextYA`) and the pure
  chain lemmas (`pieceZ_succ`, `chain_eq_sum`, `piece_recombine`, `accAfter_eq_chain`, …)
  are framework-agnostic `Fp`/`Point`/spec-level facts, proven in full by the donor. They
  reference only `Halo2.Ironwood.Specs.Sinsemilla` (the SHARED spec layer Ironwood already imports)
  and `Halo2.Ironwood.Ecc.DoubleAndAdd`. Lifted here unchanged.
-/

namespace Halo2.Ironwood.Sinsemilla

open Halo2.Ironwood (Point)
open Halo2.Ironwood.Ecc (DoubleAndAddRow)
open Halo2.Ironwood.Specs.Sinsemilla (Generators step hashToPoint)
open Halo2.Ironwood.Specs (K)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

/-! ## The generator table

Three single-column `loadTable` ops, one per S-table column (`table_idx`, `table_x`,
`table_y`), all of length `2^K`. Row `r < 2^K` holds `(r, S(r).x, S(r).y)`. -/

/-- Rust `GeneratorTableConfig` (`generator_table.rs:18-22`): the three fixed lookup
columns of the Sinsemilla generator table. -/
structure GeneratorTableConfig where
  tableIdx : TableColumn
  tableX : TableColumn
  tableY : TableColumn

/-- The generator table loader (Rust `GeneratorTableConfig::load`, `generator_table.rs:86-96`,
which fills all three columns over `[0, 2^K)` from `SINSEMILLA_S`). Three `loadTable` ops,
one per column, sharing the row index `r`:
- `tableIdx` ← `[0, 1, …, 2^K−1]`
- `tableX`   ← `[S(0).x, S(1).x, …]`
- `tableY`   ← `[S(0).y, S(1).y, …]`

This is the three-`loadTable` route (see module docs); it is a plain `Circuit … Unit`,
mirroring `LookupRangeCheck.load`. -/
def load (G : Generators) (cfg : GeneratorTableConfig) : Circuit Fp Unit := do
  loadTable cfg.tableIdx ((List.range (2 ^ K)).map (Nat.cast : ℕ → Fp))
  loadTable cfg.tableX ((List.range (2 ^ K)).map (fun j => (G.S j).x))
  loadTable cfg.tableY ((List.range (2 ^ K)).map (fun j => (G.S j).y))

/-- The generator-table-contents predicate a Sinsemilla consumer's `EnvAssumptions`
references — the three-column analogue of `LookupRangeCheck.TableLoaded`. Three conjuncts
(mirroring `TableLoaded`'s design; discharged by `load_generatorTableLoaded`):

1. **Domain-size fact** — `2^K ≤ env.usableRows` (layout data; completeness bounds its
   membership witnesses with it).
2. **Usable-rows spec** — *every* usable row holds a generator triple `(m, S(m).x, S(m).y)`
   for some `m < 2^K`. Soundness consumes this: the membership existential's witness row is
   bounded only by `env.usableRows`, and rows in `[2^K, usableRows)` carry the default-fill
   (row 0's `(0, S(0).x, S(0).y)` — still a generator triple). This is the donor
   `generatorTable.Spec` (`∃ m < 2^K, row = (m, S(m).x, S(m).y)`), over the whole domain.
3. **Block exact contents** — row `r ∈ [0, 2^K)` holds exactly `(r, S(r).x, S(r).y)`.
   Completeness consumes this to witness the membership at the honest word's own row. -/
def GeneratorTableLoaded (G : Generators) (cfg : GeneratorTableConfig)
    (env : Environment Fp) : Prop :=
  2 ^ K ≤ env.usableRows ∧
  (∀ t : ℕ, t < env.usableRows → ∃ m : ℕ, m < 2 ^ K ∧
    env.fixed cfg.tableIdx.inner (t : ℤ) = (m : Fp) ∧
    env.fixed cfg.tableX.inner (t : ℤ) = (G.S m).x ∧
    env.fixed cfg.tableY.inner (t : ℤ) = (G.S m).y) ∧
  (∀ r : ℕ, r < 2 ^ K →
    env.fixed cfg.tableIdx.inner (r : ℤ) = (r : Fp) ∧
    env.fixed cfg.tableX.inner (r : ℤ) = (G.S r).x ∧
    env.fixed cfg.tableY.inner (r : ℤ) = (G.S r).y)

private theorem pow_two_pos (n : ℕ) : 0 < 2 ^ n := pow_pos (by norm_num) n

/-- The three `loadTable` operations of `load`, at index `i`. Each `loadTable` leaves the
region index unchanged, so the do-block's operations are exactly these three, in order.
Holds by `rfl` via the monad's `operations_bind` + `nextRegionIndex_loadTable`. -/
theorem load_operations (G : Generators) (cfg : GeneratorTableConfig) (i : RegionIndex) :
    (load G cfg).operations i =
      [ .loadTable cfg.tableIdx ((List.range (2 ^ K)).map (Nat.cast : ℕ → Fp)),
        .loadTable cfg.tableX ((List.range (2 ^ K)).map (fun j => (G.S j).x)),
        .loadTable cfg.tableY ((List.range (2 ^ K)).map (fun j => (G.S j).y)) ] := rfl

/-- Contents of the `tableIdx` column: block row `r ∈ [0, 2^K)` holds `↑r`. Proven from the
`loadTable` explicit-block conjunct alone (mirrors `LookupRangeCheck.load_tableIdx_eq`). -/
theorem load_tableIdx_eq (G : Generators) (cfg : GeneratorTableConfig)
    (place : RegionIndex → ℕ) (env : Environment Fp) (i : RegionIndex)
    (h : Halo2.Constraints place env ((load G cfg).operations i) i) :
    ∀ r : ℕ, r < 2 ^ K → env.fixed cfg.tableIdx.inner (r : ℤ) = (r : Fp) := by
  rw [load_operations] at h
  simp only [Halo2.Constraints] at h
  obtain ⟨hexplicit, _⟩ := h
  intro r hr
  -- keep the length symbolic so the (concrete `K = 10`) list `List.range 1024` never
  -- reduces under `getElem!_pos` (which would blow the recursion stack)
  set N := 2 ^ K with hN; clear_value N
  have hlen : r < ((List.range N).map (Nat.cast : ℕ → Fp)).length := by
    rw [List.length_map, List.length_range]; exact hr
  have hval : ((List.range N).map (Nat.cast : ℕ → Fp))[r]! = (r : Fp) := by
    rw [getElem!_pos _ r hlen, List.getElem_map, List.getElem_range]
  rw [hexplicit r hlen, hval]

/-- Contents of the `tableX` column: block row `r` holds `S(r).x`. -/
theorem load_tableX_eq (G : Generators) (cfg : GeneratorTableConfig)
    (place : RegionIndex → ℕ) (env : Environment Fp) (i : RegionIndex)
    (h : Halo2.Constraints place env ((load G cfg).operations i) i) :
    ∀ r : ℕ, r < 2 ^ K → env.fixed cfg.tableX.inner (r : ℤ) = (G.S r).x := by
  rw [load_operations] at h
  simp only [Halo2.Constraints] at h
  -- structure: (idx_expl ∧ idx_fill ∧ (x_expl ∧ x_fill ∧ (y_expl ∧ y_fill ∧ True)))
  obtain ⟨_, _, hexplicit, _⟩ := h
  intro r hr
  set N := 2 ^ K with hN; clear_value N
  have hlen : r < ((List.range N).map (fun j => (G.S j).x)).length := by
    rw [List.length_map, List.length_range]; exact hr
  have hval : ((List.range N).map (fun j => (G.S j).x))[r]! = (G.S r).x := by
    rw [getElem!_pos _ r hlen, List.getElem_map, List.getElem_range]
  rw [hexplicit r hlen, hval]

/-- Contents of the `tableY` column: block row `r` holds `S(r).y`. -/
theorem load_tableY_eq (G : Generators) (cfg : GeneratorTableConfig)
    (place : RegionIndex → ℕ) (env : Environment Fp) (i : RegionIndex)
    (h : Halo2.Constraints place env ((load G cfg).operations i) i) :
    ∀ r : ℕ, r < 2 ^ K → env.fixed cfg.tableY.inner (r : ℤ) = (G.S r).y := by
  rw [load_operations] at h
  simp only [Halo2.Constraints] at h
  -- structure: (idx_expl ∧ idx_fill ∧ (x_expl ∧ x_fill ∧ (y_expl ∧ y_fill ∧ True)))
  obtain ⟨_, _, _, _, hexplicit, _⟩ := h
  intro r hr
  set N := 2 ^ K with hN; clear_value N
  have hlen : r < ((List.range N).map (fun j => (G.S j).y)).length := by
    rw [List.length_map, List.length_range]; exact hr
  have hval : ((List.range N).map (fun j => (G.S j).y))[r]! = (G.S r).y := by
    rw [getElem!_pos _ r hlen, List.getElem_map, List.getElem_range]
  rw [hexplicit r hlen, hval]

/-- Default-fill contents: rows in `[2^K, usableRows)` of all three columns hold the row-0
values `(0, S(0).x, S(0).y)` (the floor planner's `fill_from_row`; `lookup-design.md` §1.3.1).
Extracted from the three `loadTable`s' fill conjuncts. -/
theorem load_fill_eq (G : Generators) (cfg : GeneratorTableConfig)
    (place : RegionIndex → ℕ) (env : Environment Fp) (i : RegionIndex)
    (h : Halo2.Constraints place env ((load G cfg).operations i) i) :
    ∀ t : ℕ, 2 ^ K ≤ t → t < env.usableRows →
      env.fixed cfg.tableIdx.inner (t : ℤ) = ((0 : ℕ) : Fp) ∧
      env.fixed cfg.tableX.inner (t : ℤ) = (G.S 0).x ∧
      env.fixed cfg.tableY.inner (t : ℤ) = (G.S 0).y := by
  rw [load_operations] at h
  simp only [Halo2.Constraints] at h
  obtain ⟨_, hIdxF, _, hXF, _, hYF, -⟩ := h
  intro t hKt ht
  set N := 2 ^ K with hN
  have hNpos : 0 < N := by rw [hN]; exact pow_two_pos K
  clear_value N
  -- non-emptiness and lengths of the three loaded lists
  have hne : ∀ {α : Type} (f : ℕ → α), (List.range N).map f ≠ [] := by
    intro α f hnil
    simp only [List.map_eq_nil_iff, List.range_eq_nil] at hnil
    omega
  have hlen : ∀ {α : Type} (f : ℕ → α), ((List.range N).map f).length ≤ t := by
    intro α f; rw [List.length_map, List.length_range]; exact hKt
  have hlen0 : ∀ {α : Type} (f : ℕ → α), 0 < ((List.range N).map f).length := by
    intro α f; rw [List.length_map, List.length_range]; exact hNpos
  have hget0 : ∀ {α : Type} [Inhabited α] (f : ℕ → α), ((List.range N).map f)[0]! = f 0 := by
    intro α _ f
    rw [getElem!_pos _ 0 (hlen0 f), List.getElem_map, List.getElem_range]
  exact ⟨by rw [hIdxF (hne _) t (hlen _) ht, hget0],
         by rw [hXF (hne _) t (hlen _) ht, hget0],
         by rw [hYF (hne _) t (hlen _) ht, hget0]⟩

/-- **`load` ⇒ `GeneratorTableLoaded`**: the three loaders' `Constraints` discharge the
whole predicate. The domain-size fact `2^K ≤ env.usableRows` is layout data the load
constraints cannot force (as in `LookupRangeCheck.load_tableLoaded`), so it is a hypothesis.
The usable-rows spec (conjunct 2): block rows are their own generator triple; fill rows
carry row 0's triple `(0, S(0).x, S(0).y)`. -/
theorem load_generatorTableLoaded (G : Generators) (cfg : GeneratorTableConfig)
    (place : RegionIndex → ℕ) (env : Environment Fp) (i : RegionIndex)
    (hUsable : 2 ^ K ≤ env.usableRows)
    (h : Halo2.Constraints place env ((load G cfg).operations i) i) :
    GeneratorTableLoaded G cfg env := by
  have hblock : ∀ r : ℕ, r < 2 ^ K →
      env.fixed cfg.tableIdx.inner (r : ℤ) = (r : Fp) ∧
      env.fixed cfg.tableX.inner (r : ℤ) = (G.S r).x ∧
      env.fixed cfg.tableY.inner (r : ℤ) = (G.S r).y := fun r hr =>
    ⟨load_tableIdx_eq G cfg place env i h r hr,
     load_tableX_eq G cfg place env i h r hr,
     load_tableY_eq G cfg place env i h r hr⟩
  refine ⟨hUsable, ?_, hblock⟩
  intro t ht
  by_cases hb : t < 2 ^ K
  · exact ⟨t, hb, hblock t hb⟩
  · obtain ⟨hIdx0, hX0, hY0⟩ := load_fill_eq G cfg place env i h t (by omega) ht
    exact ⟨0, pow_two_pos K, hIdx0, hX0, hY0⟩

/-! ## Pure piece value-algebra (lifted from the donor `Clean/Orchard/Sinsemilla/HashToPoint.lean`)

All framework-agnostic: `Fp` / `Point` / `Halo2.Ironwood.Specs.Sinsemilla` facts. Names kept
identical to the donor so slice 2+ can grep-map. -/

/-! ### Pure running-sum / recombination lemmas (donor-proven, lifted verbatim) -/

theorem pieceWord_lt (p : Fp) (r : ℕ) : pieceWord p r < 2 ^ K :=
  Nat.mod_lt _ (by norm_num [K])

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

/-- Telescoped base-`2^K` running sum (donor `HashPiece.chain_eq_sum`). -/
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

/-- A piece that fits in `K·m` bits is the base-`2^K` recombination of its `K`-bit words.
Donor `HashPiece.piece_recombine`. -/
theorem piece_recombine (p : Fp) (m : ℕ) (hp : p.val < 2 ^ (K * m)) :
    p = ((∑ r ∈ Finset.range m, pieceWord p r * 2 ^ (K * r) : ℕ) : Fp) := by
  have hzn : pieceZ p m = 0 := by simp only [pieceZ, Nat.div_eq_of_lt hp, Nat.cast_zero]
  have h := chain_eq_sum (n := m) (pieceZ p) (pieceWord p) (fun r _ => pieceZ_succ p r) hzn
  rwa [pieceZ_zero] at h

/-- Each running sum `z_r` is the recombination of the words from position `r` onward.
Donor `HashPiece.chain_eq_suffix_sum`. -/
theorem chain_eq_suffix_sum {w : ℕ} (zV : ℕ → Fp) (ms : ℕ → ℕ)
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

/-! ### The Sinsemilla step bridges (donor-proven, lifted verbatim)

Pure `Point`/`Fp` facts routing the double-and-add row equations to the spec-level step
`(A ⸭ S(m)) ⸭ A = B`. `step_coordinates_of_constraints` is the soundness bridge (from gate
constraints to output coordinates), `step_honest` the completeness bridge (from the honest
`rowValue` assignments to the gate invariants and the chain point), and `accAfter_eq_chain`
lifts a whole honest piece to the spec-level `hashToPoint` chain. All lifted from the donor
`Clean/Orchard/Sinsemilla/HashToPoint.lean`. -/

/-- For one Sinsemilla step, the row equations determine the output coordinates.
Donor `HashPiece.step_coordinates_of_constraints`. -/
theorem step_coordinates_of_constraints (S : ℕ → Point Fp) {A B : Point Fp} {m : ℕ}
    (hstep : step S m A = some B)
    {xp lambda1 lambda2 xa' YA' : Fp}
    (hYP : 2 * A.y - 2 * lambda1 * (A.x - xp) = 2 * (S m).y)
    (hXP : xp = (S m).x)
    (hYA : 2 * A.y = (lambda1 + lambda2) * (A.x - (lambda1 * lambda1 - A.x - xp)))
    (hSecant : lambda2 * lambda2 = xa' + (lambda1 * lambda1 - A.x - xp) + A.x)
    (hYCheck : 4 * lambda2 * (A.x - xa') = 4 * A.y + 2 * YA') :
    xa' = B.x ∧ YA' = 2 * B.y := by
  exact Halo2.Ironwood.Ecc.DoubleAndAdd.coordinates_of_constraints (S := S m)
    (by simpa [step] using hstep) hYP hXP hYA hSecant hYCheck

/-- The honest-prover counterpart of `step_coordinates_of_constraints`: the honest cell
values (the `rowValue` assignment formulas, given as hypotheses) satisfy the row's lookup-`y`
derivation and `Y_A` invariant, and the next accumulator is `B`. Donor `HashPiece.step_honest`. -/
theorem step_honest (S : ℕ → Point Fp) {A B : Point Fp} {m : ℕ}
    (hstep : step S m A = some B)
    {l1 l2 xa' ya' : Fp}
    (hl1 : l1 = (A.y - (S m).y) * (A.x - (S m).x)⁻¹)
    (hl2 : l2 = 2 * A.y * (A.x - (l1 * l1 - A.x - (S m).x))⁻¹ - l1)
    (hxa : xa' = l2 * l2 - A.x - (l1 * l1 - A.x - (S m).x))
    (hya : ya' = l2 * (A.x - xa') - A.y) :
    A.y - l1 * (A.x - (S m).x) = (S m).y ∧
    2 * A.y = (l1 + l2) * (A.x - (l1 * l1 - A.x - (S m).x)) ∧
    xa' = B.x ∧ ya' = B.y := by
  unfold step Point.doubleAndAdd at hstep
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
  have hRadd := Point.nondegenerateAdd_eq_add
    (p := { x := A.x, y := A.y }) (q := { x := (S m).x, y := (S m).y })
    (point_ne_zero hA0) (point_ne_zero hS0) hAxS
  rw [← hR_def] at hRadd
  have hRx := congrArg Point.x hRadd
  have hRy := congrArg Point.y hRadd
  simp only [Point.nondegenerateAdd] at hRx hRy
  set slope₁ : Fp := ((S m).y - A.y) * ((S m).x - A.x)⁻¹ with hslope₁
  have hAxS' : A.x - (S m).x ≠ 0 := sub_ne_zero.mpr hAxS
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
  have hYA : 2 * A.y = (l1 + l2) * (A.x - (l1 * l1 - A.x - (S m).x)) := by
    rw [hxR, hl2, hxR]
    have hc := mul_inv_cancel₀ hRxA'
    linear_combination (-(2 * A.y)) * hc
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
  have hBx' : xa' = B.x := by
    rw [← hBx, hxa, hl2', hxR]
    ring
  have hBy' : ya' = B.y := by
    rw [hl2'] at hline₂
    rw [hya, hBx', ← hBy, hl2', hBx]
    linear_combination hline₂
  exact ⟨hyp, hYA, hBx', hBy'⟩

/-- The honest accumulator chain follows the spec-level chain points, whenever the
spec-level chain is defined. Donor `HashPiece.accAfter_eq_chain`. -/
theorem accAfter_eq_chain (G : Generators) {A : Point Fp} (p : Fp)
    {r : ℕ} {Ar : Point Fp}
    (hchain : hashToPoint G.S A ((List.range r).map (pieceWord p)) = some Ar) :
    accAfter G (A.x, A.y) p r = (Ar.x, Ar.y) := by
  induction r generalizing Ar with
  | zero =>
    rw [show ((List.range 0).map (pieceWord p)) = ([] : List ℕ) from rfl,
      Halo2.Ironwood.Specs.Sinsemilla.hashToPoint_nil] at hchain
    obtain rfl : A = Ar := Option.some.inj hchain
    rfl
  | succ r ih =>
    rw [List.range_succ] at hchain
    simp only [List.map_append, List.map_cons, List.map_nil] at hchain
    rw [Halo2.Ironwood.Specs.Sinsemilla.hashToPoint_concat] at hchain
    cases hpre : hashToPoint G.S A ((List.range r).map (pieceWord p)) with
    | none =>
      rw [hpre] at hchain
      simp at hchain
    | some Ap =>
      rw [hpre] at hchain
      replace hchain : step G.S (pieceWord p r) Ap = some Ar := hchain
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

end Halo2.Ironwood.Sinsemilla
