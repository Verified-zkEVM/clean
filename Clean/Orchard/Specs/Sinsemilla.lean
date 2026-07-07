import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Specs.CompElliptic.Curves.Pasta
import Clean.Orchard.Specs.Bitrange

/-!
# Sinsemilla value-level specification

References:
- Zcash protocol specification §5.4.1.9 (`SinsemillaHashToPoint`, `SinsemillaHash`)
- `sinsemilla@0.1` crate (`src/addition.rs`, `src/lib.rs`), the reference
  implementation used by `orchard` and by halo2's conformance tests

Sinsemilla is defined over *incomplete* addition `⸭ : P ∪ {⊥} × P ∪ {⊥} → P ∪ {⊥}`:
the result is `⊥` whenever an operand is `⊥` or the group identity, or the two points
have colliding `x`-coordinates (equal or opposite points); otherwise it agrees with the
group operation. The hash is the `⊥`-propagating chain

    Acc ← Q(D);  for each K-bit chunk mᵢ:  Acc ← (Acc ⸭ S(mᵢ)) ⸭ Acc

and `SinsemillaHash` extracts the `x`-coordinate (`Extract⊥`, with the identity mapped
to zero — our affine encoding of the identity is `(0, 0)`, so plain `.x` agrees).

The hash is a partial function by design: the protocol assumes it is infeasible to find
inputs hashing to `⊥` (finding one yields a discrete logarithm relation, protocol spec
Theorem 5.4.4). Circuit completeness statements therefore assume the hashed message is
non-exceptional, i.e. the spec-level hash is defined.
-/

namespace Orchard.Specs.Sinsemilla

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass

/-- Maximum number of chunks in a Sinsemilla message (`sinsemilla::C`). -/
def C : ℕ := 253

/-- One Sinsemilla chunk step: `(acc ⸭ S(m)) ⸭ acc`. -/
def step (S : ℕ → Point Fp) (m : ℕ) (acc : Point Fp) : Option (Point Fp) :=
  Point.doubleAndAdd acc (S m)

/-- `SinsemillaHashToPoint` over a list of `K`-bit chunk values, starting from the
domain point `Q`. Padding of bit-level messages into chunks (`pad` in the protocol
spec) is part of message construction and happens before this function. -/
def hashToPoint (S : ℕ → Point Fp) (Q : Point Fp) (chunks : List ℕ) : Option (Point Fp) :=
  chunks.foldl (fun acc m => acc.bind (step S m)) (some Q)

variable {S : ℕ → Point Fp} {Q : Point Fp}

/-- `SinsemillaHash`: the `x`-coordinate of the hash point. Our affine encoding maps
the identity to `(0, 0)`, so `.x` is exactly `Extract⊥` on defined results. -/
def hash (S : ℕ → Point Fp) (Q : Point Fp) (chunks : List ℕ) : Option Fp :=
  (hashToPoint S Q chunks).map (·.x)

/--
The Sinsemilla generator constants: the per-chunk generators
`S(j) = GroupHash("z.cash:SinsemillaS", j)` for `j < 2^K`, packaged with the property
the circuit needs from them. Group hashing never returns the identity, so all table
generators are proper curve points.
-/
structure Generators where
  S : ℕ → Point Fp
  S_onCurve : ∀ {k : ℕ}, k < 2 ^ K → (S k).OnCurve

lemma Generators.valid (G : Generators) {k : ℕ} (hk : k < 2 ^ K) : (G.S k).Valid :=
  Or.inl (G.S_onCurve hk)

/-! ### Chain lemmas -/

theorem hashToPoint_nil (S : ℕ → Point Fp) (Q : Point Fp) :
    hashToPoint S Q [] = some Q := rfl

private theorem foldl_none (S : ℕ → Point Fp) (ms : List ℕ) :
    ms.foldl (fun acc m => acc.bind (step S m)) none = none := by
  induction ms with
  | nil => rfl
  | cons m ms ih => exact ih

theorem hashToPoint_cons (S : ℕ → Point Fp) (Q : Point Fp)
    (m : ℕ) (ms : List ℕ) :
    hashToPoint S Q (m :: ms)
      = (step S m Q).bind fun acc => hashToPoint S acc ms := by
  show List.foldl _ (step S m Q) ms = _
  cases h : step S m Q with
  | none =>
    show List.foldl _ none ms = none
    exact foldl_none S ms
  | some acc =>
    rfl

theorem hashToPoint_append (S : ℕ → Point Fp) (Q : Point Fp)
    (l₁ l₂ : List ℕ) :
    hashToPoint S Q (l₁ ++ l₂)
      = (hashToPoint S Q l₁).bind fun acc => hashToPoint S acc l₂ := by
  show List.foldl _ _ (l₁ ++ l₂) = _
  rw [List.foldl_append]
  show List.foldl _ (hashToPoint S Q l₁) l₂ = _
  cases h : hashToPoint S Q l₁ with
  | none =>
    show List.foldl _ none l₂ = none
    exact foldl_none S l₂
  | some acc =>
    rfl

/-- A defined step never lands on the identity: its second incomplete addition
excludes the colliding `x`-coordinates of equal-or-opposite points. -/
theorem step_ne_zero {G : Generators} {A B : Point Fp} (a_valid : A.Valid)
    {m : ℕ} (hm : m < 2 ^ K) (h : step G.S m A = some B) : B ≠ 0 := by
  simp only [step, Point.doubleAndAdd, Option.bind_eq_bind] at h
  by_cases hc₁ : A = 0 ∨ G.S m = 0 ∨ A.x = (G.S m).x
  · rw [Point.incompleteAdd_def, if_pos hc₁] at h
    simp at h
  rw [Point.incompleteAdd_def, if_neg hc₁] at h
  rw [show ((some (A + G.S m)).bind fun t => Point.incompleteAdd t A)
    = Point.incompleteAdd (A + G.S m) A from rfl] at h
  by_cases hc₂ : A + G.S m = 0 ∨ A = 0 ∨ (A + G.S m).x = A.x
  · rw [Point.incompleteAdd_def, if_pos hc₂] at h
    simp at h
  rw [Point.incompleteAdd_def, if_neg hc₂] at h
  push Not at hc₂
  obtain rfl : A + G.S m + A = B := Option.some.inj h
  intro h0
  replace h0 : A.toSW a_valid + (G.S m).toSW (G.valid hm) + A.toSW a_valid = 0 := by
    simp only [← Point.toSW_zero, ← Point.toSW_add, h0]
  rw [add_eq_zero_iff_eq_neg] at h0
  have h2 : (A.toSW a_valid + (G.S m).toSW (G.valid hm)).x ≠ (A.toSW a_valid).x := by
    simp_rw [← Point.toSW_add, Point.toSW_x]
    exact hc₂.2.2
  exact h2 (by rw [h0, SWPoint.neg_x])

/-- A defined step from a valid accumulator lands on a valid point. -/
theorem step_valid {G : Generators} {A B : Point Fp} (a_valid : A.Valid)
    {m : ℕ} (hm : m < 2 ^ K) (h : step G.S m A = some B) : B.Valid := by
  simp only [step, Point.doubleAndAdd, Option.bind_eq_bind] at h
  by_cases hc₁ : A = 0 ∨ G.S m = 0 ∨ A.x = (G.S m).x
  · rw [Point.incompleteAdd_def, if_pos hc₁] at h
    simp at h
  rw [Point.incompleteAdd_def, if_neg hc₁] at h
  rw [show ((some (A + G.S m)).bind fun t => Point.incompleteAdd t A)
    = Point.incompleteAdd (A + G.S m) A from rfl] at h
  by_cases hc₂ : A + G.S m = 0 ∨ A = 0 ∨ (A + G.S m).x = A.x
  · rw [Point.incompleteAdd_def, if_pos hc₂] at h
    simp at h
  rw [Point.incompleteAdd_def, if_neg hc₂] at h
  obtain rfl : A + G.S m + A = B := Option.some.inj h
  exact Point.valid_add (Point.valid_add a_valid (G.valid hm)) a_valid

/-- Chain points of a defined hash are never the identity. -/
theorem hashToPoint_ne_zero {G : Generators} {Q B : Point Fp}
    {l : List ℕ} (hQvalid : Q.Valid) (hQ : Q ≠ 0) (hl : ∀ m ∈ l, m < 2 ^ K)
    (h : hashToPoint G.S Q l = some B) : B ≠ 0 := by
  induction l generalizing Q with
  | nil =>
    rw [hashToPoint_nil] at h
    exact Option.some.inj h ▸ hQ
  | cons m ms ih =>
    rw [hashToPoint_cons] at h
    cases hs : step G.S m Q with
    | none =>
      rw [hs] at h
      simp at h
    | some C =>
      rw [hs] at h
      exact ih (step_valid hQvalid (hl m (by simp)) hs)
        (step_ne_zero hQvalid (hl m (by simp)) hs)
        (fun n hn => hl n (by simp [hn])) h

theorem hashToPoint_valid {G : Generators} {Q B : Point Fp}
    {l : List ℕ} (hQvalid : Q.Valid) (hl : ∀ m ∈ l, m < 2 ^ K)
    (h : hashToPoint G.S Q l = some B) : B.Valid := by
  induction l generalizing Q with
  | nil =>
    rw [hashToPoint_nil] at h
    exact Option.some.inj h ▸ hQvalid
  | cons m ms ih =>
    rw [hashToPoint_cons] at h
    cases hs : step G.S m Q with
    | none =>
      rw [hs] at h
      simp at h
    | some C =>
      rw [hs] at h
      exact ih (step_valid hQvalid (hl m (by simp)) hs)
        (fun n hn => hl n (by simp [hn])) h

/-- Split a defined chain at a list boundary. -/
theorem hashToPoint_append_some {S : ℕ → Point Fp}
    {Q B : Point Fp} {l₁ l₂ : List ℕ}
    (h : hashToPoint S Q (l₁ ++ l₂) = some B) :
    ∃ C, hashToPoint S Q l₁ = some C ∧ hashToPoint S C l₂ = some B := by
  rw [hashToPoint_append] at h
  cases hc : hashToPoint S Q l₁ with
  | none =>
    rw [hc] at h
    simp at h
  | some C =>
    rw [hc] at h
    exact ⟨C, rfl, h⟩

/-- Peel the last step off a chain. -/
theorem hashToPoint_concat (S : ℕ → Point Fp) (Q : Point Fp)
    (l : List ℕ) (m : ℕ) :
    hashToPoint S Q (l ++ [m])
      = (hashToPoint S Q l).bind fun acc => step S m acc := by
  rw [hashToPoint_append]
  cases h : hashToPoint S Q l with
  | none => rfl
  | some acc =>
    show hashToPoint S acc [m] = step S m acc
    rw [hashToPoint_cons]
    cases h : step S m acc with
    | none => rfl
    | some b => rfl

/-! ### The `MerkleCRH` message -/

/--
The 52 `K`-bit chunks of the `MerkleCRH^Orchard` message `l⋆ || left⋆ || right⋆`
(10 + 255 + 255 bits, little-endian; protocol spec §5.4.1.3), given 255-bit
little-endian encodings `lv`, `rv` of the two child nodes. The encodings may be
non-canonical (the circuit only constrains 255 bits, matching the source).
-/
def merkleChunks (l lv rv : ℕ) : List ℕ :=
  (List.range 52).map fun i => (l + 2 ^ 10 * lv + 2 ^ 265 * rv) / 2 ^ (K * i) % 2 ^ K

/-! ### `K`-bit chunking -/

/-- The `n` little-endian `K`-bit chunks of `val`. -/
def chunksOf (val n : ℕ) : List ℕ :=
  (List.range n).map fun i => bitrange val (K * i) K

@[simp] theorem chunksOf_length (val n : ℕ) : (chunksOf val n).length = n := by
  simp [chunksOf]

/-- Split a chunk list at position `m`: the low `m` chunks of `val`, then the chunks of
the part above bit `K*m`. -/
theorem chunksOf_add (val m n : ℕ) :
    chunksOf val (m + n) = chunksOf val m ++ chunksOf (val / 2 ^ (K * m)) n := by
  unfold chunksOf
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, bitrange_div]
  congr 2
  ring

/-- Chunks below position `n` are unaffected by reducing `val` mod `2 ^ (K * n)`. -/
theorem chunksOf_mod (val n : ℕ) : chunksOf (val % 2 ^ (K * n)) n = chunksOf val n := by
  unfold chunksOf
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  exact bitrange_mod (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left K hi)

theorem chunksOf_eq_of_mod_eq {a b n : ℕ} (h : a % 2 ^ (K * n) = b % 2 ^ (K * n)) :
    chunksOf a n = chunksOf b n := by
  rw [← chunksOf_mod a n, ← chunksOf_mod b n, h]

/-! ### Recovering chunk lists from `K`-bit digit sums

These generic lemmas turn a field element written as a `K`-bit digit sum
`∑ ms r · 2^(K·r)` into the statement that `chunksOf` recovers exactly those digits `ms`.
They are the arithmetic core shared by the `note_commit` and `commit_ivk` message-piece
soundness bridges (which read the digit functions out of `Chain.PieceChunks`). -/

/-- Peel the head digit off a `K`-bit (here `Kb`-bit) digit sum. -/
theorem sum_head_shift (Kb m : ℕ) (d : ℕ → ℕ) :
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

/-- A `Kb`-bit digit sum of length `n` is bounded by `2^(Kb·n)`. -/
theorem sum_digits_lt {Kb : ℕ} {d : ℕ → ℕ} (hd : ∀ j, d j < 2 ^ Kb) (n : ℕ) :
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

/-- The `i`-th `Kb`-bit digit of a digit sum is `d i`. -/
theorem digit_of_sum (Kb : ℕ) :
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

/-- `chunksOf` recovers the `K`-bit digits of a value written as their digit sum. -/
theorem chunksOf_eq_map_of_sum {value n : ℕ} {ms : ℕ → ℕ}
    (hms : ∀ r, ms r < 2 ^ K)
    (hvalue : value = ∑ r ∈ Finset.range n, ms r * 2 ^ (K * r)) :
    chunksOf value n = (List.range n).map ms := by
  apply List.ext_getElem
  · simp [chunksOf]
  intro i hi hi'
  have hin : i < n := by
    simp only [chunksOf, List.length_map, List.length_range] at hi
    exact hi
  rw [show (chunksOf value n)[i] = value / 2 ^ (K * i) % 2 ^ K from by
    simp [chunksOf, bitrange]]
  rw [hvalue]
  simp only [List.getElem_map, List.getElem_range]
  exact digit_of_sum K i n ms hms hin

/-- The field-cast form of `chunksOf_eq_map_of_sum`: a digit-sum equality over the base
field (with both sides below the field cardinality) recovers the chunks. -/
theorem chunksOf_eq_map_of_cast_sum {value n : ℕ} {ms : ℕ → ℕ}
    (hms : ∀ r, ms r < 2 ^ K)
    (hcast :
      (value : CompElliptic.Fields.Pasta.PallasBaseField) =
        ((∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) :
          CompElliptic.Fields.Pasta.PallasBaseField))
    (hvalueCard : value < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    (hsumCard : (∑ r ∈ Finset.range n, ms r * 2 ^ (K * r) : ℕ) <
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) :
    chunksOf value n = (List.range n).map ms := by
  apply chunksOf_eq_map_of_sum hms
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hvalueCard, ZMod.val_natCast_of_lt hsumCard] at hval
  exact hval

/-- A one-chunk decomposition is a singleton. -/
theorem chunksOf_one_eq_singleton {x : ℕ} (hx : x < 2 ^ K) :
    chunksOf x 1 = [x] := by
  unfold chunksOf bitrange
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, pow_zero, Nat.div_one]
  rw [Nat.mod_eq_of_lt hx]

/-- Dividing a `Kb`-bit digit sum by `2^(Kb·r)` drops its low `r` digits (the suffix sum).
This is the value-level fact behind a Sinsemilla running-sum cell `z_r = piece >> (K·r)`. -/
theorem sum_suffix_div {Kb : ℕ} {d : ℕ → ℕ} (hd : ∀ j, d j < 2 ^ Kb) :
    ∀ (m r : ℕ), r ≤ m →
      (∑ j ∈ Finset.range m, d j * 2 ^ (Kb * j)) / 2 ^ (Kb * r)
        = ∑ j ∈ Finset.range (m - r), d (r + j) * 2 ^ (Kb * j) := by
  intro m r
  induction r generalizing m d with
  | zero => intro _; simp
  | succ r ih =>
    intro hr
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [sum_head_shift,
      show Kb * (r + 1) = Kb + Kb * r from by ring, pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos Kb), Nat.div_eq_of_lt (hd 0), Nat.zero_add,
      ih (d := fun j => d (j + 1)) (fun j => hd (j + 1)) m' (by omega),
      show m' + 1 - (r + 1) = m' - r from by omega]
    exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_right_comm]

/-- A `Kb`-bit running sum telescopes: if `z i = w_i + 2^Kb · z (i+1)` with each `w_i` a
`Kb`-bit word, then `z 0 = lo + 2^(Kb·r) · z r` for a low `r`-word value `lo < 2^(Kb·r)`.
This is the soundness content of a `LookupRangeCheck.CopyCheck` running sum: `z r = 0`
forces `z 0 < 2^(Kb·r)`. -/
theorem running_sum_telescope (Kb : ℕ)
    (z : ℕ → CompElliptic.Fields.Pasta.PallasBaseField) :
    ∀ r : ℕ, (∀ i, i < r → ∃ w : ℕ, w < 2 ^ Kb ∧
        z i = ((w : ℕ) : CompElliptic.Fields.Pasta.PallasBaseField)
          + ((2 ^ Kb : ℕ) : CompElliptic.Fields.Pasta.PallasBaseField) * z (i + 1)) →
      ∃ lo : ℕ, lo < 2 ^ (Kb * r) ∧
        z 0 = ((lo : ℕ) : CompElliptic.Fields.Pasta.PallasBaseField)
          + ((2 ^ (Kb * r) : ℕ) : CompElliptic.Fields.Pasta.PallasBaseField) * z r := by
  intro r
  induction r with
  | zero => intro _; exact ⟨0, by positivity, by simp⟩
  | succ r ih =>
    intro hstep
    obtain ⟨lo, hlo, hz0⟩ := ih (fun i hi => hstep i (by omega))
    obtain ⟨w, hw, hzr⟩ := hstep r (by omega)
    refine ⟨lo + 2 ^ (Kb * r) * w, ?_, ?_⟩
    · have : 2 ^ (Kb * r) * w + 2 ^ (Kb * r) ≤ 2 ^ (Kb * (r + 1)) := by
        rw [show Kb * (r + 1) = Kb * r + Kb from by ring, pow_add]
        calc 2 ^ (Kb * r) * w + 2 ^ (Kb * r) = 2 ^ (Kb * r) * (w + 1) := by ring
          _ ≤ 2 ^ (Kb * r) * 2 ^ Kb := Nat.mul_le_mul_left _ (by omega)
      omega
    · rw [hz0, hzr,
        show Kb * (r + 1) = Kb * r + Kb from by ring, pow_add]
      push_cast
      ring

/-! ### The `NoteCommit` message -/

/--
The 109 `K`-bit chunks of the Orchard `NoteCommit^Orchard` message
`g★_d || pk★_d || i2lebsp₆₄(v) || rho || psi`
(protocol spec §3.7 / §5.4.8.4, `note_commit.rs`), assembled little-endian as the bit
string

```
  x(g_d) [255]  ỹ(g_d) [1]  x(pk_d) [255]  ỹ(pk_d) [1]  v [64]  rho [255]  psi [255]  0000 [4 pad]
```

= 1090 bits = 109 chunks. `gdX`, `pkdX`, `rho`, `psi` are the (≤255-bit, little-endian)
x-coordinate / base-field encodings; `gdY`, `pkdY` are the `ỹ` sign bits; `v` is the 64-bit
note value. The encodings may be non-canonical — the hash circuit constrains 255-bit
ranges; canonicity is enforced separately by the `NoteCommit input *` gates. The final
4 zero bits are the `h_2` padding of message piece `h`. -/
def noteCommitMessage (gdX gdY pkdX pkdY v rho psi : ℕ) : ℕ :=
  gdX + 2 ^ 255 * gdY + 2 ^ 256 * pkdX + 2 ^ 511 * pkdY
    + 2 ^ 512 * v + 2 ^ 576 * rho + 2 ^ 831 * psi

def noteCommitChunks (gdX gdY pkdX pkdY v rho psi : ℕ) : List ℕ :=
  chunksOf (noteCommitMessage gdX gdY pkdX pkdY v rho psi) 109

/-- The 109 message chunks tile into the 8 Sinsemilla message pieces `a..h` at their
`K`-bit boundaries: piece sizes `25, 1, 25, 6, 1, 25, 25, 1` chunks starting at bits
`0, 250, 260, 510, 570, 580, 830, 1080`. -/
theorem noteCommitChunks_tiling (gdX gdY pkdX pkdY v rho psi : ℕ) :
    noteCommitChunks gdX gdY pkdX pkdY v rho psi =
      chunksOf (noteCommitMessage gdX gdY pkdX pkdY v rho psi) 25
        ++ chunksOf (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 250) 1
        ++ chunksOf (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 260) 25
        ++ chunksOf (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 510) 6
        ++ chunksOf (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 570) 1
        ++ chunksOf (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 580) 25
        ++ chunksOf (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 830) 25
        ++ chunksOf (noteCommitMessage gdX gdY pkdX pkdY v rho psi / 2 ^ 1080) 1 := by
  unfold noteCommitChunks
  set m := noteCommitMessage gdX gdY pkdX pkdY v rho psi
  rw [show (109 : ℕ) = 25 + 84 from rfl, chunksOf_add,
      show (84 : ℕ) = 1 + 83 from rfl, chunksOf_add,
      show (83 : ℕ) = 25 + 58 from rfl, chunksOf_add,
      show (58 : ℕ) = 6 + 52 from rfl, chunksOf_add,
      show (52 : ℕ) = 1 + 51 from rfl, chunksOf_add,
      show (51 : ℕ) = 25 + 26 from rfl, chunksOf_add,
      show (26 : ℕ) = 25 + 1 from rfl, chunksOf_add]
  simp only [Nat.div_div_eq_div_mul, ← pow_add, K, Nat.reduceMul, Nat.reduceAdd,
    List.append_assoc]

/-- The `CommitIvk` Sinsemilla message `I2LEBSP₂₅₅(ak) || I2LEBSP₂₅₅(nk)` (protocol spec
§5.4.8.4, `commit_ivk.rs`), assembled little-endian as `ak [255] || nk [255]` = 510 bits.
`ak`, `nk` are the (≤255-bit, little-endian) base-field encodings; the encodings may be
non-canonical, with canonicity enforced separately by the `CommitIvk` gate. -/
def commitIvkMessage (ak nk : ℕ) : ℕ :=
  ak + 2 ^ 255 * nk

/-- The 51 `K`-bit chunks of the `CommitIvk` message (510 bits = 51 chunks). -/
def commitIvkChunks (ak nk : ℕ) : List ℕ :=
  chunksOf (commitIvkMessage ak nk) 51

/-- The 51 message chunks tile into the 4 Sinsemilla message pieces `a, b, c, d` at their
`K`-bit boundaries: piece sizes `25, 1, 24, 1` chunks starting at bits `0, 250, 260, 500`. -/
theorem commitIvkChunks_tiling (ak nk : ℕ) :
    commitIvkChunks ak nk =
      chunksOf (commitIvkMessage ak nk) 25
        ++ chunksOf (commitIvkMessage ak nk / 2 ^ 250) 1
        ++ chunksOf (commitIvkMessage ak nk / 2 ^ 260) 24
        ++ chunksOf (commitIvkMessage ak nk / 2 ^ 500) 1 := by
  unfold commitIvkChunks
  set m := commitIvkMessage ak nk
  rw [show (51 : ℕ) = 25 + 26 from rfl, chunksOf_add,
      show (26 : ℕ) = 1 + 25 from rfl, chunksOf_add]
  simp only [Nat.div_div_eq_div_mul, ← pow_add, K, Nat.reduceMul, Nat.reduceAdd]
  nth_rewrite 2 [show (25 : ℕ) = 24 + 1 from rfl]
  rw [chunksOf_add]
  simp only [Nat.div_div_eq_div_mul, ← pow_add, K, Nat.reduceMul, Nat.reduceAdd,
    List.append_assoc]

end Orchard.Specs.Sinsemilla
