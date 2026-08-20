import Clean.Ironwood.Specs.PallasCert
import Clean.Ironwood.Ecc.MulFixed.Theorems
import Clean.Ironwood.Ecc.MulFixed.ShortTheorems

/-!
# Nat-level certification checker for concrete fixed-base window tables

The evaluation layer of the concrete-`FixedBase` certification. All checked equations
live over `ℕ` literals (`rfl`-evaluable through GMP kernel arithmetic — the ZMod-stated
equivalents are >200× slower, see `BenchFixedBase.lean`); the soundness lemmas here
bridge each passed check into the `Point Fp` facts (`PallasCert`) the chain induction
consumes. Subtraction is encoded as `(a + P − b) % P`. Per-base checks use neither
inversion nor exponentiation: slopes and non-square quotient roots are witnesses, after
one shared kernel check establishes that `13` is a non-square.
-/

namespace Zcash.Circuits.Ecc.MulFixed.Cert

open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

/-- The Pallas base-field modulus (the checker's `ℕ` world). -/
abbrev P : ℕ := PALLAS_BASE_CARD

/-- `a·b mod P`. -/
def mulm (a b : ℕ) : ℕ := a * b % P

/-- `a − b mod P` (offset spelling, total on `ℕ`). -/
def subm (a b : ℕ) : ℕ := (a + P - b) % P

/-! ## Cast bridges (ℕ checks → `Fp` equations) -/

theorem cast_mod (a : ℕ) : ((a % P : ℕ) : Fp) = (a : Fp) := ZMod.natCast_mod a P

theorem cast_mulm (a b : ℕ) : ((mulm a b : ℕ) : Fp) = (a : Fp) * (b : Fp) := by
  rw [mulm, cast_mod]
  push_cast
  ring

theorem cast_subm {b : ℕ} (a : ℕ) (hb : b ≤ P) :
    ((subm a b : ℕ) : Fp) = (a : Fp) - (b : Fp) := by
  rw [subm, cast_mod, Nat.cast_sub (by omega), Nat.cast_add,
    show ((P : ℕ) : Fp) = 0 from ZMod.natCast_self P]
  ring

theorem cast_inj {a b : ℕ} (ha : a < P) (hb : b < P) (h : (a : Fp) = (b : Fp)) :
    a = b := by
  have h' : ZMod.val (n := PALLAS_BASE_CARD) (a : Fp) = ZMod.val (n := PALLAS_BASE_CARD) (b : Fp) :=
    congrArg _ h
  rwa [ZMod.val_cast_of_lt (show a < PALLAS_BASE_CARD from ha),
    ZMod.val_cast_of_lt (show b < PALLAS_BASE_CARD from hb)] at h'

theorem cast_eq_zero_iff {a : ℕ} (ha : a < P) : ((a : Fp) = 0) ↔ a = 0 := by
  constructor
  · intro h
    exact cast_inj ha (by norm_num [P, PALLAS_BASE_CARD]) (by rw [h]; norm_num)
  · intro h
    rw [h]
    norm_num

/-! ## Single-op checkers -/

/-- Secant addition check: `⟨px,py⟩ + ⟨qx,qy⟩ = ⟨rx,ry⟩` with slope witness `l`. -/
def checkAdd (px py qx qy l rx ry : ℕ) : Bool :=
  px < P && py < P && qx < P && qy < P && l < P && rx < P && ry < P &&
  !(px == 0 && py == 0) && !(qx == 0 && qy == 0) && !(px == qx) &&
  mulm l (subm qx px) == subm qy py &&
  rx == subm (mulm l l) ((px + qx) % P) &&
  ry == subm (mulm l (subm px rx)) py

/-- Tangent doubling check: `⟨px,py⟩ + ⟨px,py⟩ = ⟨rx,ry⟩` with slope witness `l`
(`pallasA = 0`). -/
def checkDouble (px py l rx ry : ℕ) : Bool :=
  px < P && py < P && l < P && rx < P && ry < P &&
  !(px == 0 && py == 0) && !(py == 0) &&
  mulm l (2 * py % P) == 3 * px * px % P &&
  rx == subm (mulm l l) ((px + px) % P) &&
  ry == subm (mulm l (subm px rx)) py

/-- The `Point Fp` of a `ℕ` coordinate pair. -/
def pointOf (c : ℕ × ℕ) : Point Fp := ⟨(c.1 : Fp), (c.2 : Fp)⟩

theorem pointOf_ne_zero {x y : ℕ} (hx : x < P) (hy : y < P)
    (h : ¬(x = 0 ∧ y = 0)) : pointOf (x, y) ≠ 0 := by
  intro h0
  have hx0 : ((x : ℕ) : Fp) = 0 := congrArg Point.x h0
  have hy0 : ((y : ℕ) : Fp) = 0 := congrArg Point.y h0
  exact h ⟨(cast_eq_zero_iff hx).mp hx0, (cast_eq_zero_iff hy).mp hy0⟩

/-- Soundness of `checkAdd`. -/
theorem checkAdd_sound {px py qx qy l rx ry : ℕ}
    (h : checkAdd px py qx qy l rx ry = true) :
    pointOf (px, py) + pointOf (qx, qy) = pointOf (rx, ry) := by
  simp only [checkAdd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpx, hpy⟩, hqx⟩, hqy⟩, hl⟩, hrx⟩, hry⟩, hpz⟩, hqz⟩, hne⟩,
    h1⟩, h2⟩, h3⟩ := h
  have hPle : ∀ {a : ℕ}, a < P → a ≤ P := fun h => Nat.le_of_lt h
  apply Point.add_of_witness (l := (l : Fp))
  · exact pointOf_ne_zero hpx hpy (by
      intro ⟨h1', h2'⟩
      simp [h1', h2'] at hpz)
  · exact pointOf_ne_zero hqx hqy (by
      intro ⟨h1', h2'⟩
      simp [h1', h2'] at hqz)
  · show ((px : ℕ) : Fp) ≠ ((qx : ℕ) : Fp)
    intro hc
    exact absurd (cast_inj hpx hqx hc) (by simpa using hne)
  · show (l : Fp) * (((qx : ℕ) : Fp) - ((px : ℕ) : Fp))
      = ((qy : ℕ) : Fp) - ((py : ℕ) : Fp)
    have := congrArg (Nat.cast (R := Fp)) h1
    rwa [cast_mulm, cast_subm _ (hPle hpx), cast_subm _ (hPle hpy)] at this
  · show ((rx : ℕ) : Fp) = (l : Fp) * (l : Fp) - ((px : ℕ) : Fp) - ((qx : ℕ) : Fp)
    have := congrArg (Nat.cast (R := Fp)) h2
    rw [cast_subm _ (by
        have : (px + qx) % P < P := Nat.mod_lt _ (by norm_num [P, PALLAS_BASE_CARD])
        omega),
      cast_mulm, cast_mod] at this
    push_cast at this
    rw [this]
    ring
  · show ((ry : ℕ) : Fp)
      = (l : Fp) * (((px : ℕ) : Fp) - ((rx : ℕ) : Fp)) - ((py : ℕ) : Fp)
    have := congrArg (Nat.cast (R := Fp)) h3
    rwa [cast_subm _ (hPle hpy), cast_mulm, cast_subm _ (hPle hrx)] at this

/-- Soundness of `checkDouble`. -/
theorem checkDouble_sound {px py l rx ry : ℕ}
    (h : checkDouble px py l rx ry = true) :
    pointOf (px, py) + pointOf (px, py) = pointOf (rx, ry) := by
  simp only [checkDouble, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpx, hpy⟩, hl⟩, hrx⟩, hry⟩, hpz⟩, hyz⟩, h1⟩, h2⟩, h3⟩ := h
  have hPle : ∀ {a : ℕ}, a < P → a ≤ P := fun h => Nat.le_of_lt h
  apply Point.double_of_witness (l := (l : Fp))
  · exact pointOf_ne_zero hpx hpy (by
      intro ⟨h1', h2'⟩
      simp [h1', h2'] at hpz)
  · show ((py : ℕ) : Fp) ≠ 0
    intro hc
    exact hyz ((cast_eq_zero_iff hpy).mp hc)
  · show (l : Fp) * (2 * ((py : ℕ) : Fp)) = 3 * ((px : ℕ) : Fp) ^ 2 + pallasA
    have := congrArg (Nat.cast (R := Fp)) h1
    rw [cast_mulm, cast_mod] at this
    rw [show ((3 * px * px % P : ℕ) : Fp) = ((3 * px * px : ℕ) : Fp) from cast_mod _]
      at this
    push_cast at this
    rw [this, pallasA]
    ring
  · show ((rx : ℕ) : Fp) = (l : Fp) * (l : Fp) - ((px : ℕ) : Fp) - ((px : ℕ) : Fp)
    have := congrArg (Nat.cast (R := Fp)) h2
    rw [cast_subm _ (by
        have : (px + px) % P < P := Nat.mod_lt _ (by norm_num [P, PALLAS_BASE_CARD])
        omega),
      cast_mulm, cast_mod] at this
    push_cast at this
    rw [this]
    ring
  · show ((ry : ℕ) : Fp)
      = (l : Fp) * (((px : ℕ) : Fp) - ((rx : ℕ) : Fp)) - ((py : ℕ) : Fp)
    have := congrArg (Nat.cast (R := Fp)) h3
    rwa [cast_subm _ (hPle hpy), cast_mulm, cast_subm _ (hPle hrx)] at this

/-! ## Chain checkers (row / window fold) and their soundness -/

namespace Chain

open Point

/-- Check a row tail: successive entries step by the fixed point `S`
(`entry + S = next`, secant with witnessed slope). -/
def checkRow (S : ℕ × ℕ) (prev : ℕ × ℕ) : List ((ℕ × ℕ) × ℕ) → Bool
  | [] => true
  | (r, l) :: rest =>
      checkAdd prev.1 prev.2 S.1 S.2 l r.1 r.2 && checkRow S r rest

/-- Check one window: entry 0 is the doubling `S + S`, the rest a `checkRow`. -/
def checkWindow (S : ℕ × ℕ) : List ((ℕ × ℕ) × ℕ) → Bool
  | [] => false
  | (p0, l0) :: rest => checkDouble S.1 S.2 l0 p0.1 p0.2 && checkRow S p0 rest

/-- Check a list of windows, threading the step point `S_{w+1} = row_w[6]`
(the `k = 6` entry is `8·8^w·B`). -/
def checkWindows (S : ℕ × ℕ) : List (List ((ℕ × ℕ) × ℕ)) → Bool
  | [] => true
  | row :: rest =>
      checkWindow S row &&
      match row[6]? with
      | some (s', _) => checkWindows s' rest
      | none => false

theorem one_nsmul_point (p : Point Fp) : (1 : ℕ) • p = p := by
  rw [Point.nsmul_def]
  show Point.ofCoords
    (CompElliptic.CurveForms.ShortWeierstrass.add _ ((0 : ℕ) • p).coords p.coords) = p
  rw [show ((0 : ℕ) • p).coords = ((0 : Fp), (0 : Fp)) from rfl,
    CompElliptic.CurveForms.ShortWeierstrass.zero_add]
  rfl

theorem checkRow_sound {B : Point Fp} (hB : B.OnCurve) {S : ℕ × ℕ} {s : ℕ}
    (hS : pointOf S = s • B) (row : List ((ℕ × ℕ) × ℕ)) :
    ∀ (prev : ℕ × ℕ) (a : ℕ),
      pointOf prev = a • B → checkRow S prev row = true →
      ∀ i, (hi : i < row.length) → pointOf row[i].1 = (a + (i + 1) * s) • B := by
  induction row with
  | nil => intro _ _ _ _ i hi; simp at hi
  | cons e rest ih =>
      obtain ⟨r, l⟩ := e
      intro prev a hprev h i hi
      simp only [checkRow, Bool.and_eq_true] at h
      have hr : pointOf r = (a + s) • B := by
        rw [← Point.nsmul_add_nsmul hB, ← hprev, ← hS]
        exact (checkAdd_sound h.1).symm
      match i with
      | 0 => simpa using hr
      | Nat.succ i =>
          simp only [List.getElem_cons_succ]
          rw [show a + (i + 1 + 1) * s = (a + s) + (i + 1) * s from by ring]
          exact ih r (a + s) hr h.2 i (by simpa using hi)

theorem checkWindow_sound {B : Point Fp} (hB : B.OnCurve) {S : ℕ × ℕ} {s : ℕ}
    (hS : pointOf S = s • B) {row : List ((ℕ × ℕ) × ℕ)}
    (h : checkWindow S row = true) :
    ∀ i, (hi : i < row.length) → pointOf row[i].1 = ((i + 2) * s) • B := by
  cases row with
  | nil => simp [checkWindow] at h
  | cons e rest =>
      obtain ⟨p0, l0⟩ := e
      simp only [checkWindow, Bool.and_eq_true] at h
      have h0 : pointOf p0 = (2 * s) • B := by
        rw [show 2 * s = s + s from by ring, ← Point.nsmul_add_nsmul hB, ← hS]
        exact (checkDouble_sound h.1).symm
      intro i hi
      match i with
      | 0 => simpa using h0
      | Nat.succ i =>
          simp only [List.getElem_cons_succ]
          rw [show (i + 1 + 2) * s = 2 * s + (i + 1) * s from by ring]
          exact checkRow_sound hB hS rest p0 (2 * s) h0 h.2 i (by simpa using hi)

theorem checkWindows_sound {B : Point Fp} (hB : B.OnCurve)
    (rows : List (List ((ℕ × ℕ) × ℕ))) :
    ∀ (S : ℕ × ℕ) (s : ℕ),
      pointOf S = s • B → checkWindows S rows = true →
      ∀ w, (hw : w < rows.length) → ∀ i, (hi : i < rows[w].length) →
        pointOf (rows[w][i]).1 = ((i + 2) * (8 ^ w * s)) • B := by
  induction rows with
  | nil => intro _ _ _ _ w hw; simp at hw
  | cons row rest ih =>
      intro S s hS h w hw i hi
      simp only [checkWindows, Bool.and_eq_true] at h
      obtain ⟨hwin, hnext⟩ := h
      match w with
      | 0 =>
          have := checkWindow_sound hB hS hwin i (by simpa using hi)
          simpa using this
      | Nat.succ w =>
          match hrow6 : row[6]? with
          | none => rw [hrow6] at hnext; exact absurd hnext (by simp)
          | some e =>
              rw [hrow6] at hnext
              obtain ⟨hlen, hval⟩ := List.getElem?_eq_some_iff.mp hrow6
              have h6 : pointOf e.1 = (8 * s) • B := by
                have := checkWindow_sound hB hS hwin 6 hlen
                rw [hval] at this
                simpa using this
              simp only [List.getElem_cons_succ]
              rw [show (i + 2) * (8 ^ (w + 1) * s) = (i + 2) * (8 ^ w * (8 * s))
                from by ring]
              exact ih e.1 (8 * s) h6 hnext w (by simpa using hw) i
                (by simpa using hi)

/-! ### Negation and variable-step rows (the MSB window's offset chain) -/

/-- Negation check: `⟨rx,ry⟩ = −⟨tx,ty⟩`. -/
def checkNeg (tx ty rx ry : ℕ) : Bool :=
  tx < P && ty < P && rx < P && ry < P && rx == tx && ry == subm 0 ty

theorem checkNeg_sound {tx ty rx ry : ℕ} (h : checkNeg tx ty rx ry = true) :
    -(pointOf (tx, ty)) = pointOf (rx, ry) := by
  simp only [checkNeg, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨htx, hty⟩, hrx⟩, hry⟩, hx⟩, hy⟩ := h
  apply Point.neg_of_witness
  · show ((rx : ℕ) : Fp) = ((tx : ℕ) : Fp)
    rw [hx]
  · show ((ry : ℕ) : Fp) = -((ty : ℕ) : Fp)
    have := congrArg (Nat.cast (R := Fp)) hy
    rwa [cast_subm _ (Nat.le_of_lt hty), Nat.cast_zero, zero_sub] at this

/-- Cancellation transport: if `p + q = 0` for valid points, `q = −p`. -/
theorem eq_neg_of_add_eq_zero {p q : Point Fp}
    (hp : p.Valid) (hq : q.Valid) (h : p + q = 0) : q = -p := by
  have hsw := (Point.ext_toSW_iff (Point.valid_add hp hq)
    Point.valid_zero).mp h
  rw [Point.toSW_add hp hq, Point.toSW_zero] at hsw
  rw [Point.ext_toSW_iff hq (Point.valid_neg hp),
    Point.toSW_neg hp]
  exact eq_neg_of_add_eq_zero_right hsw

/-- `m • B = −(n • B)` whenever `n + m ≡ 0` mod the group order. -/
theorem nsmul_eq_neg_nsmul {B : Point Fp} (hB : B.OnCurve) {n m : ℕ}
    (h : (n + m) % CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD = 0) :
    m • B = -(n • B) := by
  have hz : (n + m) • B = 0 := by
    rw [Point.nsmul_eq_zero_iff hB]
    exact Nat.dvd_of_mod_eq_zero h
  rw [← Point.nsmul_add_nsmul hB] at hz
  exact eq_neg_of_add_eq_zero (Point.valid_nsmul (.inl hB) n)
    (Point.valid_nsmul (.inl hB) m) hz

/-- A row whose step point varies per entry: `prev + q_j = r_j` (the offset `T`-chain). -/
def checkVarRow (prev : ℕ × ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ) × ℕ) → Bool
  | [] => true
  | (q, r, l) :: rest =>
      checkAdd prev.1 prev.2 q.1 q.2 l r.1 r.2 && checkVarRow r rest

theorem checkVarRow_sound {B : Point Fp} (hB : B.OnCurve)
    (entries : List ((ℕ × ℕ) × (ℕ × ℕ) × ℕ)) :
    ∀ (prev : ℕ × ℕ) (c : ℕ) (f : ℕ → ℕ),
      pointOf prev = c • B →
      (∀ j, (hj : j < entries.length) → pointOf entries[j].1 = f j • B) →
      checkVarRow prev entries = true →
      ∀ j, (hj : j < entries.length) →
        pointOf entries[j].2.1 = (c + ∑ i ∈ Finset.range (j + 1), f i) • B := by
  induction entries with
  | nil => intro _ _ _ _ _ _ j hj; simp at hj
  | cons e rest ih =>
      obtain ⟨q, r, l⟩ := e
      intro prev c f hprev hf h j hj
      simp only [checkVarRow, Bool.and_eq_true] at h
      have hr : pointOf r = (c + f 0) • B := by
        rw [← Point.nsmul_add_nsmul hB, ← hprev,
          ← hf 0 (by simp)]
        exact (checkAdd_sound h.1).symm
      match j with
      | 0 => simpa using hr
      | Nat.succ j =>
          simp only [List.getElem_cons_succ]
          have := ih r (c + f 0) (fun i => f (i + 1)) hr
            (fun i hi => by
              have := hf (i + 1) (by simpa using hi)
              simpa using this)
            h.2 j (by simpa using hj)
          rw [this]
          congr 1
          conv_rhs => rw [Finset.sum_range_succ']
          ring

/-! ### The whole-base certificate -/

/-- A dumped window-table certificate: the base point, the lower windows (each 8
entries with step slopes), the offset `T`-chain (addend, `T_j`, slope — addends must
equal `rows[j+1][0]`), and the MSB row (entry 0 the negated offset with unused slope,
then 7 steps). -/
structure BaseCert where
  base : ℕ × ℕ
  rows : List (List ((ℕ × ℕ) × ℕ))
  tChain : List ((ℕ × ℕ) × (ℕ × ℕ) × ℕ)
  msb : List ((ℕ × ℕ) × ℕ)

/-- Full chain check for a base with `numLower + 1` windows. -/
def checkBase (numLower : ℕ) (c : BaseCert) : Bool :=
  (c.rows.length == numLower) &&
  c.rows.all (fun row => row.length == 8) &&
  (c.msb.length == 8) &&
  (c.tChain.length + 1 == numLower) &&
  checkWindows c.base c.rows &&
  checkVarRow (c.rows[0]!)[0]!.1 c.tChain &&
  (List.range c.tChain.length).all (fun j =>
    c.tChain[j]!.1 == (c.rows[j + 1]!)[0]!.1) &&
  checkNeg (c.tChain[c.tChain.length - 1]!).2.1.1 (c.tChain[c.tChain.length - 1]!).2.1.2
    (c.msb[0]!).1.1 (c.msb[0]!).1.2 &&
  checkRow ((c.rows[numLower - 1]!)[6]!).1 (c.msb[0]!).1 (c.msb.drop 1)

open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD) in
/-- Chain soundness for the whole certificate: every lower-window entry is
`((k+2)·8^w)·B`, and every MSB entry is `(a₀ + k·8^numLower)·B` where `a₀` represents
`−(Σ_{j<numLower} 2·8^j)` mod the group order. -/
theorem checkBase_sound {numLower : ℕ} (hnl : 6 < numLower) {c : BaseCert}
    (hB : (pointOf c.base).OnCurve) (h : checkBase numLower c = true) :
    (∀ w, (hw : w < numLower) → ∀ k, (hk : k < 8) →
      ∃ (hw' : w < c.rows.length) (hk' : k < c.rows[w].length),
        pointOf (c.rows[w][k]).1 = ((k + 2) * 8 ^ w) • pointOf c.base) ∧
    (∀ k, (hk : k < 8) →
      ∃ (hk' : k < c.msb.length),
        pointOf (c.msb[k]).1 =
          ((PALLAS_SCALAR_CARD -
              (∑ j ∈ Finset.range numLower, 2 * 8 ^ j) % PALLAS_SCALAR_CARD)
            + k * 8 ^ numLower) • pointOf c.base) := by
  simp only [checkBase, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlen, hrow8⟩, hmsb8⟩, htlen⟩, hwins⟩, htv⟩, hmatch⟩, hneg⟩,
    hmsbrow⟩ := h
  set B := pointOf c.base with hBdef
  have hB1 : pointOf c.base = (1 : ℕ) • B := (one_nsmul_point B).symm
  have hlower : ∀ w, (hw : w < c.rows.length) → ∀ k, (hk : k < c.rows[w].length) →
      pointOf (c.rows[w][k]).1 = ((k + 2) * 8 ^ w) • B := by
    intro w hw k hk
    have := checkWindows_sound hB c.rows c.base 1 hB1 hwins w hw k hk
    simpa using this
  have hrowlen : ∀ w, (hw : w < c.rows.length) → c.rows[w].length = 8 := by
    intro w hw
    exact hrow8 _ (c.rows.getElem_mem hw)
  have card_pos : 0 < PALLAS_SCALAR_CARD := by
    norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]
  refine ⟨?_, ?_⟩
  · intro w hw k hk
    have hw' : w < c.rows.length := by rw [hlen]; exact hw
    exact ⟨hw', by rw [hrowlen w hw']; exact hk,
      hlower w hw' k (by rw [hrowlen w hw']; exact hk)⟩
  · -- ── the MSB window ──
    have gpR : ∀ i, (h : i < c.rows.length) → c.rows[i]! = c.rows[i] :=
      fun i h => getElem!_pos c.rows i h
    have gpT : ∀ i, (h : i < c.tChain.length) → c.tChain[i]! = c.tChain[i] :=
      fun i h => getElem!_pos c.tChain i h
    have gpM : ∀ i, (h : i < c.msb.length) → c.msb[i]! = c.msb[i] :=
      fun i h => getElem!_pos c.msb i h
    have gpE : ∀ (l : List ((ℕ × ℕ) × ℕ)) i, (h : i < l.length) → l[i]! = l[i] :=
      fun l i h => getElem!_pos l i h
    set S : ℕ := ∑ j ∈ Finset.range numLower, 2 * 8 ^ j with hSdef
    have h0r : 0 < c.rows.length := by rw [hlen]; omega
    have h0r0 : 0 < c.rows[0].length := by rw [hrowlen 0 h0r]; omega
    -- T-chain start = rows[0][0] = 2·B
    have hp00 : pointOf ((c.rows[0]!)[0]!).1 = (2 : ℕ) • B := by
      rw [gpR 0 h0r, gpE _ 0 h0r0]
      have := hlower 0 h0r 0 h0r0
      simpa using this
    -- T-chain addend values
    have hf : ∀ j, (hj : j < c.tChain.length) →
        pointOf c.tChain[j].1 = (2 * 8 ^ (j + 1)) • B := by
      intro j hj
      have hm := hmatch j hj
      have hjr : j + 1 < c.rows.length := by rw [hlen]; omega
      have hjr0 : 0 < c.rows[j + 1].length := by rw [hrowlen _ hjr]; omega
      rw [gpT j hj, gpR _ hjr, gpE _ 0 hjr0] at hm
      rw [hm]
      have := hlower (j + 1) hjr 0 hjr0
      simpa using this
    -- T-chain results
    have htvr : checkVarRow ((c.rows[0]!)[0]!).1 c.tChain = true := htv
    have hT := checkVarRow_sound hB c.tChain ((c.rows[0]!)[0]!).1 2
      (fun j => 2 * 8 ^ (j + 1)) hp00 hf htvr
    -- the last T is the whole offset sum
    have hlpos : 0 < c.tChain.length := by omega
    have hTlast : pointOf (c.tChain[c.tChain.length - 1]!).2.1 = S • B := by
      rw [gpT _ (by omega)]
      have := hT (c.tChain.length - 1) (by omega)
      rw [this]
      congr 1
      rw [hSdef, ← htlen, show c.tChain.length - 1 + 1 = c.tChain.length from by omega,
        Finset.sum_range_succ']
      ring
    -- msb[0] = −(S·B)
    have hmod : (S + (PALLAS_SCALAR_CARD - S % PALLAS_SCALAR_CARD))
        % PALLAS_SCALAR_CARD = 0 := by
      have hd := Nat.div_add_mod S PALLAS_SCALAR_CARD
      have hlt : S % PALLAS_SCALAR_CARD < PALLAS_SCALAR_CARD := Nat.mod_lt _ card_pos
      have heq : S + (PALLAS_SCALAR_CARD - S % PALLAS_SCALAR_CARD)
          = PALLAS_SCALAR_CARD * (S / PALLAS_SCALAR_CARD) + PALLAS_SCALAR_CARD := by
        omega
      rw [heq, ← Nat.mul_succ, Nat.mul_mod_right]
    have hm0 : pointOf (c.msb[0]!).1
        = (PALLAS_SCALAR_CARD - S % PALLAS_SCALAR_CARD) • B := by
      have hn := checkNeg_sound hneg
      have : pointOf (c.msb[0]!).1 = -(S • B) := by
        rw [← hTlast]
        exact hn.symm
      rw [this]
      exact (nsmul_eq_neg_nsmul hB hmod).symm
    -- top step point = 8^numLower · B
    have htoplen : numLower - 1 < c.rows.length := by rw [hlen]; omega
    have htop6 : 6 < c.rows[numLower - 1].length := by rw [hrowlen _ htoplen]; omega
    have htop : pointOf (((c.rows[numLower - 1]!)[6]!)).1 = (8 ^ numLower) • B := by
      rw [gpR _ htoplen, gpE _ 6 htop6]
      have := hlower (numLower - 1) htoplen 6 htop6
      rw [this]
      congr 1
      rw [show (6 + 2 : ℕ) = 8 from rfl,
        show 8 * 8 ^ (numLower - 1) = 8 ^ (numLower - 1 + 1) from by
          rw [pow_succ]; ring,
        show numLower - 1 + 1 = numLower from by omega]
    -- the msb row
    have hrow := checkRow_sound hB htop (c.msb.drop 1) (c.msb[0]!).1
      (PALLAS_SCALAR_CARD - S % PALLAS_SCALAR_CARD) hm0 hmsbrow
    intro k hk
    have hk' : k < c.msb.length := by rw [hmsb8]; exact hk
    refine ⟨hk', ?_⟩
    match k with
    | 0 =>
        rw [← gpM 0 hk']
        simpa using hm0
    | Nat.succ k =>
        have hkd : k < (c.msb.drop 1).length := by
          rw [List.length_drop, hmsb8]
          omega
        have := hrow k hkd
        simp only [List.getElem_drop, show 1 + k = k + 1 from by omega] at this
        rw [this]

/-! ### The `windowPoint` bridge (85-window scalars) -/

/-- The certified table entry for window `w`, value `k` (of a base with
`numLower + 1` windows). -/
def certEntry (numLower : ℕ) (c : BaseCert) (w k : ℕ) : ℕ × ℕ :=
  if w < numLower then ((c.rows[w]!)[k]!).1 else (c.msb[k]!).1

open CompElliptic.Fields.Pasta (Fq PALLAS_SCALAR_CARD)

theorem windowScalar_val_lower {w k : ℕ} (hw : w < 84) (hk : k < 8) :
    (Ecc.MulFixed.windowScalar w k).val = (k + 2) * 8 ^ w := by
  rw [Ecc.MulFixed.windowScalar, if_neg (by omega)]
  have hcast : ((k : Fq) + 2) * 8 ^ w = (((k + 2) * 8 ^ w : ℕ) : Fq) := by
    push_cast
    ring
  rw [hcast, ZMod.val_cast_of_lt]
  calc (k + 2) * 8 ^ w ≤ 9 * 8 ^ 83 := by
        apply Nat.mul_le_mul (by omega)
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < PALLAS_SCALAR_CARD := by
        norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]

theorem offsetAcc_eq_sum :
    Ecc.MulFixed.offsetAcc = ∑ j ∈ Finset.range 84, 2 * 8 ^ j := by
  rw [Ecc.MulFixed.offsetAcc]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ' 2 (3 * j), pow_mul]
  norm_num

open Point in
/-- The full 85-window bridge: a passed `checkBase 84` certificate's entries ARE the
`windowPoint`s of its base. -/
theorem cert_windowPoint_eq {c : BaseCert}
    (hB : (pointOf c.base).OnCurve) (h : checkBase 84 c = true) :
    ∀ w, (hw : w < 85) → ∀ k, (hk : k < 8) →
      pointOf (certEntry 84 c w k)
        = Ecc.MulFixed.windowPoint (pointOf c.base) w k := by
  obtain ⟨hlow, hmsb⟩ := checkBase_sound (by omega) hB h
  intro w hw k hk
  rw [Ecc.MulFixed.windowPoint]
  by_cases hw84 : w < 84
  · obtain ⟨hw', hk', hval⟩ := hlow w hw84 k hk
    rw [certEntry, if_pos (show w < 84 from hw84), getElem!_pos c.rows w hw', getElem!_pos _ k hk', hval,
      windowScalar_val_lower hw84 hk]
  · have hw' : w = 84 := by omega
    subst hw'
    obtain ⟨hk', hval⟩ := hmsb k hk
    rw [certEntry, if_neg (by omega : ¬ 84 < 84), getElem!_pos c.msb k hk', hval]
    apply Point.nsmul_congr hB
    rw [← ZMod.natCast_eq_natCast_iff]
    set S : ℕ := ∑ j ∈ Finset.range 84, 2 * 8 ^ j with hSdef
    have hSle : S % PALLAS_SCALAR_CARD ≤ PALLAS_SCALAR_CARD :=
      Nat.le_of_lt (Nat.mod_lt _ (by norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]))
    have hcast : ((PALLAS_SCALAR_CARD - S % PALLAS_SCALAR_CARD + k * 8 ^ 84 : ℕ) : Fq)
        = (k : Fq) * 8 ^ 84 - (S : Fq) := by
      rw [Nat.cast_add, Nat.cast_sub hSle, ZMod.natCast_self,
        show ((S % PALLAS_SCALAR_CARD : ℕ) : Fq) = (S : Fq) from ZMod.natCast_mod S _]
      push_cast
      ring
    rw [hcast]
    have hws : Ecc.MulFixed.windowScalar 84 k
        = (k : Fq) * 8 ^ 84 - (S : Fq) := by
      rw [Ecc.MulFixed.windowScalar, if_pos rfl, offsetAcc_eq_sum, hSdef]
    rw [← hws]
    exact (ZMod.natCast_rightInverse _).symm

/-! ### Interpolation, u-table, Euler, and on-curve checks -/

/-- Horner evaluation of the 8 Lagrange coefficients at `k`, mod `P`. -/
def evalInterp (cs : List ℕ) (k : ℕ) : ℕ :=
  cs.foldr (fun ci acc => (ci + k * acc) % P) 0

/-- `CoordsParams` from dumped `ℕ` literals (`z`, then the 8 coefficients). -/
def mkParams (z : ℕ) (cs : List ℕ) : Ecc.MulFixed.CoordsParams Fp :=
  { z := (z : Fp), lagrange0 := (cs[0]! : Fp), lagrange1 := (cs[1]! : Fp),
    lagrange2 := (cs[2]! : Fp), lagrange3 := (cs[3]! : Fp),
    lagrange4 := (cs[4]! : Fp), lagrange5 := (cs[5]! : Fp),
    lagrange6 := (cs[6]! : Fp), lagrange7 := (cs[7]! : Fp) }

theorem evalInterp_cast (z c0 c1 c2 c3 c4 c5 c6 c7 k : ℕ) :
    ((evalInterp [c0, c1, c2, c3, c4, c5, c6, c7] k : ℕ) : Fp)
      = Ecc.MulFixed.interpolate
          (mkParams z [c0, c1, c2, c3, c4, c5, c6, c7]) (k : Fp) := by
  simp only [evalInterp, List.foldr, cast_mod, Ecc.MulFixed.interpolate,
    mkParams, List.getElem!_cons_zero, List.getElem!_cons_succ]
  push_cast [cast_mod]
  ring

/-- Interpolation check for one window: the polynomial hits all 8 table x-coords. -/
def checkInterp (cs : List ℕ) (xs : List ℕ) : Bool :=
  cs.length == 8 && xs.length == 8 &&
  (List.range 8).all fun k => evalInterp cs k == xs[k]! % P

/-- u-table check for one window: `u_k² = y_k + z`. -/
def checkU (z : ℕ) (us : List ℕ) (ys : List ℕ) : Bool :=
  us.length == 8 && ys.length == 8 &&
  (List.range 8).all fun k => mulm us[k]! us[k]! == (ys[k]! + z) % P

/-- Fuel-based binary modular exponentiation (kernel-friendly). -/
def powModAux (a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % P
  | fuel + 1, e =>
    if e = 0 then 1 % P
    else
      let h := powModAux a fuel (e / 2)
      let h2 := h * h % P
      if e % 2 = 1 then h2 * a % P else h2

def powMod (a e : ℕ) : ℕ := powModAux a 256 e

theorem powModAux_cast (a : ℕ) :
    ∀ fuel e, e < 2 ^ fuel → ((powModAux a fuel e : ℕ) : Fp) = (a : Fp) ^ e := by
  intro fuel
  induction fuel with
  | zero =>
      intro e he
      interval_cases e
      simp [powModAux]
  | succ fuel ih =>
      intro e he
      rw [powModAux]
      by_cases he0 : e = 0
      · simp [he0]
      · rw [if_neg he0]
        have hdiv : e / 2 < 2 ^ fuel := by
          have := Nat.div_lt_of_lt_mul (by
            rw [← pow_succ']
            exact he)
          omega
        have hh := ih (e / 2) hdiv
        by_cases hodd : e % 2 = 1
        · rw [if_pos hodd]
          rw [cast_mod]
          push_cast [cast_mod]
          rw [hh, ← pow_add, ← pow_succ]
          congr 1
          omega
        · rw [if_neg hodd]
          rw [cast_mod]
          push_cast
          rw [hh, ← pow_add]
          congr 1
          omega

theorem powMod_cast (a e : ℕ) (he : e < 2 ^ 256) :
    ((powMod a e : ℕ) : Fp) = (a : Fp) ^ e :=
  powModAux_cast a 256 e he

/-- Euler check: `x` is a quadratic non-residue. -/
def checkNonSquare (x : ℕ) : Bool :=
  x < P && powMod x ((P - 1) / 2) == P - 1

theorem checkNonSquare_sound {x : ℕ} (h : checkNonSquare x = true) :
    ¬ IsSquare ((x : ℕ) : Fp) := by
  simp only [checkNonSquare, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨hx, hpow⟩ := h
  have hP2 : (P : ℕ) / 2 = (P - 1) / 2 := by
    norm_num [P, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  have hebound : (P - 1) / 2 < 2 ^ 256 := by
    norm_num [P, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  have hcast := powMod_cast x ((P - 1) / 2) hebound
  rw [hpow] at hcast
  have hm1 : ((P - 1 : ℕ) : Fp) = -1 := by
    rw [Nat.cast_sub (by norm_num [P, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])]
    rw [ZMod.natCast_self]
    push_cast
    ring
  rw [hm1] at hcast
  have hxne : ((x : ℕ) : Fp) ≠ 0 := by
    intro h0
    rw [h0] at hcast
    have hne : ((P - 1 : ℕ) : ℕ) / 2 ≠ 0 := by
      norm_num [P, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    rw [zero_pow hne] at hcast
    have : (1 : Fp) = 0 := by
      have := congrArg (· + 1) hcast
      simpa using this.symm
    exact one_ne_zero this
  intro hsq
  have := (ZMod.euler_criterion _ hxne).mp hsq
  rw [hP2.symm] at hcast
  rw [this] at hcast
  have : (2 : Fp) = 0 := by linear_combination -hcast
  exact two_ne_zero this

/-- A single kernel-checked quadratic non-residue used to certify all of the fixed-base
table non-residues by multiplication with a nonzero square. -/
theorem thirteen_not_isSquare : ¬ IsSquare (13 : Fp) := by
  set_option maxRecDepth 4000 in
  exact checkNonSquare_sound (by decide +kernel)

/-- Cheap certification that `x` is a non-square: exhibit a nonzero `root` such that
`x = 13 * root²`, where `13` is the fixed non-square above. -/
def checkNonSquareRoot (x root : ℕ) : Bool :=
  root < P && !(root == 0) && mulm 13 (mulm root root) == x

theorem checkNonSquareRoot_sound {x root : ℕ}
    (h : checkNonSquareRoot x root = true) :
    ¬ IsSquare ((x : ℕ) : Fp) := by
  simp only [checkNonSquareRoot, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] at h
  obtain ⟨⟨hroot, hroot0⟩, heq⟩ := h
  have hrootFp : ((root : ℕ) : Fp) ≠ 0 := by
    intro hz
    exact hroot0 ((cast_eq_zero_iff hroot).mp hz)
  have heqFp := congrArg (Nat.cast (R := Fp)) heq
  rw [cast_mulm, cast_mulm] at heqFp
  push_cast at heqFp
  intro hxSquare
  obtain ⟨s, hs⟩ := hxSquare
  apply thirteen_not_isSquare
  refine ⟨s / (root : Fp), ?_⟩
  field_simp [hrootFp]
  calc
    13 * ((root : Fp) ^ 2) = 13 * ((root : Fp) * (root : Fp)) := by ring
    _ = (x : Fp) := heqFp
    _ = s * s := hs
    _ = s ^ 2 := by ring

/-- On-curve check for a `ℕ` point (`y² = x³ + 5`). -/
def checkOnCurve (x y : ℕ) : Bool :=
  x < P && y < P && mulm y y == (mulm (mulm x x) x + 5) % P

theorem checkOnCurve_sound {x y : ℕ} (h : checkOnCurve x y = true) :
    (pointOf (x, y)).OnCurve := by
  simp only [checkOnCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hx, hy⟩, hc⟩ := h
  have := congrArg (Nat.cast (R := Fp)) hc
  rw [cast_mulm, cast_mod] at this
  push_cast [cast_mulm] at this
  show ((y : ℕ) : Fp) ^ 2 = ((x : ℕ) : Fp) ^ 3 + pallasB
  rw [pallasB]
  rw [show ((y : ℕ) : Fp) ^ 2 = ((y : ℕ) : Fp) * ((y : ℕ) : Fp) from sq _]
  rw [this]
  ring

/-! ### The full certificate and the `FixedBase` constructors -/

/-- A full fixed-base certificate: the chain data plus the dumped `z`/coefficient/u
tables and the roots witnessing each `z - y` as `13` times a nonzero square. -/
structure FullCert extends BaseCert where
  zs : List ℕ
  coeffs : List (List ℕ)
  us : List (List ℕ)
  nonSquareRoots : List (List ℕ)

/-- The certified x/y coordinate of entry `(w, k)`. -/
def entryX (numLower : ℕ) (c : BaseCert) (w k : ℕ) : ℕ := (certEntry numLower c w k).1
def entryY (numLower : ℕ) (c : BaseCert) (w k : ℕ) : ℕ := (certEntry numLower c w k).2

/-- The whole certificate check for a base with `numLower + 1` windows. -/
def checkFull (numLower : ℕ) (c : FullCert) : Bool :=
  checkBase numLower c.toBaseCert &&
  checkOnCurve c.base.1 c.base.2 &&
  (c.zs.length == numLower + 1) &&
  (c.coeffs.length == numLower + 1) &&
  (c.us.length == numLower + 1) &&
  (c.nonSquareRoots.length == numLower + 1) &&
  (List.range (numLower + 1)).all fun w =>
    (c.coeffs[w]!.length == 8) &&
    (c.nonSquareRoots[w]!.length == 8) &&
    checkInterp c.coeffs[w]!
      ((List.range 8).map fun k => entryX numLower c.toBaseCert w k) &&
    checkU c.zs[w]! c.us[w]!
      ((List.range 8).map fun k => entryY numLower c.toBaseCert w k) &&
    (List.range 8).all fun k =>
      (entryY numLower c.toBaseCert w k < P) &&
      checkNonSquareRoot (subm c.zs[w]! (entryY numLower c.toBaseCert w k))
        ((c.nonSquareRoots[w]!)[k]!)

theorem checkBase_eq_true_of_checkFull_eq_true {numLower : ℕ} {c : FullCert}
    (h : checkFull numLower c = true) :
    checkBase numLower c.toBaseCert = true := by
  simp only [checkFull, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hbase, honc⟩, hzs⟩, hcoeffs⟩, hus⟩, hroots⟩, hwindows⟩ := h
  exact hbase

theorem checkOnCurve_eq_true_of_checkFull_eq_true {numLower : ℕ} {c : FullCert}
    (h : checkFull numLower c = true) :
    checkOnCurve c.base.1 c.base.2 = true := by
  simp only [checkFull, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hbase, honc⟩, hzs⟩, hcoeffs⟩, hus⟩, hroots⟩, hwindows⟩ := h
  exact honc

/-- The per-window facts `checkFull` certifies, at the `Fp` level. -/
theorem checkFull_window_facts {numLower : ℕ} {c : FullCert}
    (h : checkFull numLower c = true) :
    ∀ (w : ℕ), (hw : w < numLower + 1) → ∀ (k : ℕ), (hk : k < 8) →
      (Ecc.MulFixed.interpolate (mkParams c.zs[w]! c.coeffs[w]!) (k : Fp)
          = ((entryX numLower c.toBaseCert w k : ℕ) : Fp)) ∧
      (((c.us[w]!)[k]! : Fp) * ((c.us[w]!)[k]! : Fp)
          = ((entryY numLower c.toBaseCert w k : ℕ) : Fp) + ((c.zs[w]! : ℕ) : Fp)) ∧
      ¬ IsSquare (((c.zs[w]! : ℕ) : Fp) - ((entryY numLower c.toBaseCert w k : ℕ) : Fp)) := by
  simp only [checkFull, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hbase, honc⟩, hzl⟩, hcl⟩, hul⟩, hrl⟩, hwin⟩ := h
  intro w hw k hk
  obtain ⟨⟨⟨⟨hc8, hr8⟩, hinterp⟩, hu⟩, hns⟩ := hwin w hw
  refine ⟨?_, ?_, ?_⟩
  · -- interpolation
    simp only [checkInterp, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      List.mem_range] at hinterp
    obtain ⟨⟨_, _⟩, hik⟩ := hinterp
    have := hik k hk
    have hcs : ∃ c0 c1 c2 c3 c4 c5 c6 c7,
        c.coeffs[w]! = [c0, c1, c2, c3, c4, c5, c6, c7] := by
      match hval : c.coeffs[w]!, hc8 with
      | [c0, c1, c2, c3, c4, c5, c6, c7], _ =>
          exact ⟨c0, c1, c2, c3, c4, c5, c6, c7, rfl⟩
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, hcs⟩ := hcs
    rw [hcs] at this ⊢
    have hcast := congrArg (Nat.cast (R := Fp)) this
    rw [evalInterp_cast c.zs[w]! c0 c1 c2 c3 c4 c5 c6 c7 k] at hcast
    rw [hcast]
    rw [show ((List.range 8).map fun k => entryX numLower c.toBaseCert w k)[k]!
        = entryX numLower c.toBaseCert w k from by
      rw [getElem!_pos _ k (by simp; omega), List.getElem_map, List.getElem_range]]
    rw [cast_mod]
  · -- u-table
    simp only [checkU, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      List.mem_range] at hu
    obtain ⟨⟨_, _⟩, huk⟩ := hu
    have := huk k hk
    rw [show ((List.range 8).map fun k => entryY numLower c.toBaseCert w k)[k]!
        = entryY numLower c.toBaseCert w k from by
      rw [getElem!_pos _ k (by simp; omega), List.getElem_map, List.getElem_range]] at this
    have hcast := congrArg (Nat.cast (R := Fp)) this
    rw [cast_mulm, cast_mod] at hcast
    rw [hcast]
    push_cast
    ring
  · -- non-squareness
    obtain ⟨hylt, hnsk⟩ := hns k hk
    have := checkNonSquareRoot_sound hnsk
    rwa [cast_subm _ (Nat.le_of_lt (of_decide_eq_true hylt))] at this

open Point in
/-- Construct a proof-carrying `FixedBase` (85 windows) from a passed certificate. -/
def ofCert (c : FullCert) (h : checkFull 84 c = true) :
    Ecc.MulFixed.FixedBase where
  point := pointOf c.base
  onCurve := checkOnCurve_sound (checkOnCurve_eq_true_of_checkFull_eq_true h)
  params := fun w => mkParams c.zs[w]! c.coeffs[w]!
  u := fun w k => ((c.us[w]!)[k]! : Fp)
  interpolate_eq := by
    intro w hw k hk
    have hbase := checkBase_eq_true_of_checkFull_eq_true h
    have hwp := cert_windowPoint_eq
      (checkOnCurve_sound (checkOnCurve_eq_true_of_checkFull_eq_true h))
      hbase w hw k hk
    have := (checkFull_window_facts h w (by omega) k hk).1
    rw [this, ← hwp]
    rfl
  u_mul_u := by
    intro w hw k hk
    have hbase := checkBase_eq_true_of_checkFull_eq_true h
    have hwp := cert_windowPoint_eq
      (checkOnCurve_sound (checkOnCurve_eq_true_of_checkFull_eq_true h))
      hbase w hw k hk
    have := (checkFull_window_facts h w (by omega) k hk).2.1
    rw [this, ← hwp]
    rfl
  z_sub_y_not_square := by
    intro w hw k hk
    have hbase := checkBase_eq_true_of_checkFull_eq_true h
    have hwp := cert_windowPoint_eq
      (checkOnCurve_sound (checkOnCurve_eq_true_of_checkFull_eq_true h))
      hbase w hw k hk
    have := (checkFull_window_facts h w (by omega) k hk).2.2
    rw [← hwp]
    exact this

/-! ### The Short (22-window) variant -/

theorem short_windowScalar_val_lower {w k : ℕ} (hw : w < 21) (hk : k < 8) :
    (Ecc.MulFixed.Short.windowScalar w k).val = (k + 2) * 8 ^ w := by
  rw [Ecc.MulFixed.Short.windowScalar, if_neg (by omega)]
  have hcast : ((k : Fq) + 2) * 8 ^ w = (((k + 2) * 8 ^ w : ℕ) : Fq) := by
    push_cast
    ring
  rw [hcast, ZMod.val_cast_of_lt]
  calc (k + 2) * 8 ^ w ≤ 9 * 8 ^ 20 := by
        apply Nat.mul_le_mul (by omega)
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < PALLAS_SCALAR_CARD := by
        norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]

open Point in
/-- The 22-window bridge: a passed `checkBase 21` certificate's entries ARE the Short
`windowPoint`s of its base. -/
theorem cert_windowPoint_eq_short {c : BaseCert}
    (hB : (pointOf c.base).OnCurve) (h : checkBase 21 c = true) :
    ∀ (w : ℕ), (hw : w < 22) → ∀ (k : ℕ), (hk : k < 8) →
      pointOf (certEntry 21 c w k)
        = Ecc.MulFixed.Short.windowPoint (pointOf c.base) w k := by
  obtain ⟨hlow, hmsb⟩ := checkBase_sound (by omega) hB h
  intro w hw k hk
  rw [Ecc.MulFixed.Short.windowPoint]
  by_cases hw21 : w < 21
  · obtain ⟨hw', hk', hval⟩ := hlow w hw21 k hk
    rw [certEntry, if_pos (show w < 21 from hw21), getElem!_pos c.rows w hw',
      getElem!_pos _ k hk', hval, short_windowScalar_val_lower hw21 hk]
  · have hw' : w = 21 := by omega
    subst hw'
    obtain ⟨hk', hval⟩ := hmsb k hk
    rw [certEntry, if_neg (by omega : ¬ 21 < 21), getElem!_pos c.msb k hk', hval]
    apply Point.nsmul_congr hB
    rw [← ZMod.natCast_eq_natCast_iff]
    set S : ℕ := ∑ j ∈ Finset.range 21, 2 * 8 ^ j with hSdef
    have hSle : S % PALLAS_SCALAR_CARD ≤ PALLAS_SCALAR_CARD :=
      Nat.le_of_lt (Nat.mod_lt _
        (by norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]))
    have hcast : ((PALLAS_SCALAR_CARD - S % PALLAS_SCALAR_CARD + k * 8 ^ 21 : ℕ) : Fq)
        = (k : Fq) * 8 ^ 21 - (S : Fq) := by
      rw [Nat.cast_add, Nat.cast_sub hSle, ZMod.natCast_self,
        show ((S % PALLAS_SCALAR_CARD : ℕ) : Fq) = (S : Fq) from ZMod.natCast_mod S _]
      push_cast
      ring
    rw [hcast]
    have hws : Ecc.MulFixed.Short.windowScalar 21 k
        = (k : Fq) * 8 ^ 21 - (S : Fq) := by
      rw [Ecc.MulFixed.Short.windowScalar, if_pos rfl,
        Ecc.MulFixed.Short.offsetAcc_eq, hSdef]
    rw [← hws]
    exact (ZMod.natCast_rightInverse _).symm

open Point in
/-- Construct a proof-carrying `Short.FixedBase` (22 windows) from a passed certificate. -/
def ofCertShort (c : FullCert) (h : checkFull 21 c = true) :
    Ecc.MulFixed.Short.FixedBase where
  point := pointOf c.base
  onCurve := checkOnCurve_sound (checkOnCurve_eq_true_of_checkFull_eq_true h)
  params := fun w => mkParams c.zs[w]! c.coeffs[w]!
  u := fun w k => ((c.us[w]!)[k]! : Fp)
  interpolate_eq := by
    intro w hw k hk
    have hwp := cert_windowPoint_eq_short
      (checkOnCurve_sound (checkOnCurve_eq_true_of_checkFull_eq_true h))
      (checkBase_eq_true_of_checkFull_eq_true h) w hw k hk
    have := (checkFull_window_facts h w (by omega) k hk).1
    rw [this, ← hwp]
    rfl
  u_mul_u := by
    intro w hw k hk
    have hwp := cert_windowPoint_eq_short
      (checkOnCurve_sound (checkOnCurve_eq_true_of_checkFull_eq_true h))
      (checkBase_eq_true_of_checkFull_eq_true h) w hw k hk
    have := (checkFull_window_facts h w (by omega) k hk).2.1
    rw [this, ← hwp]
    rfl
  z_sub_y_not_square := by
    intro w hw k hk
    have hwp := cert_windowPoint_eq_short
      (checkOnCurve_sound (checkOnCurve_eq_true_of_checkFull_eq_true h))
      (checkBase_eq_true_of_checkFull_eq_true h) w hw k hk
    have := (checkFull_window_facts h w (by omega) k hk).2.2
    rw [← hwp]
    exact this

end Chain

export Chain (BaseCert FullCert checkBase checkFull ofCert ofCertShort)

end Zcash.Circuits.Ecc.MulFixed.Cert
