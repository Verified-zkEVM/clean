import Clean.Orchard.Specs.Elliptic.Curves.Pasta

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

/-- Number of bits per Sinsemilla message chunk (`sinsemilla::K`). -/
def K : ℕ := 10

/-- Maximum number of chunks in a Sinsemilla message (`sinsemilla::C`). -/
def C : ℕ := 253

open Classical in
/-- Incomplete addition `⸭` (protocol spec §5.4.1.9, `sinsemilla/src/addition.rs`):
`⊥` if an operand is the identity or the `x`-coordinates collide (equal or opposite
points), otherwise the group operation. `⊥` operands are handled by `Option.bind` at
use sites. -/
noncomputable def incompleteAdd (p q : SWPoint Pallas.curve) :
    Option (SWPoint Pallas.curve) :=
  if p = 0 ∨ q = 0 ∨ p.x = q.x then none else some (p + q)

/-- One Sinsemilla chunk step: `(acc ⸭ S(m)) ⸭ acc`. -/
noncomputable def step (S : ℕ → SWPoint Pallas.curve) (acc : SWPoint Pallas.curve) (m : ℕ) :
    Option (SWPoint Pallas.curve) :=
  (incompleteAdd acc (S m)).bind fun t => incompleteAdd t acc

/-- `SinsemillaHashToPoint` over a list of `K`-bit chunk values, starting from the
domain point `Q`. Padding of bit-level messages into chunks (`pad` in the protocol
spec) is part of message construction and happens before this function. -/
noncomputable def hashToPoint (S : ℕ → SWPoint Pallas.curve) (Q : SWPoint Pallas.curve)
    (chunks : List ℕ) : Option (SWPoint Pallas.curve) :=
  chunks.foldl (fun acc m => acc.bind (step S · m)) (some Q)

/-- `SinsemillaHash`: the `x`-coordinate of the hash point. Our affine encoding maps
the identity to `(0, 0)`, so `.x` is exactly `Extract⊥` on defined results. -/
noncomputable def hash (S : ℕ → SWPoint Pallas.curve) (Q : SWPoint Pallas.curve)
    (chunks : List ℕ) : Option CompElliptic.Fields.Pasta.PallasBaseField :=
  (hashToPoint S Q chunks).map (·.x)

/--
The Sinsemilla generator constants: the per-chunk generators
`S(j) = GroupHash("z.cash:SinsemillaS", j)` for `j < 2^K`, packaged with the property
the circuit needs from them. Group hashing never returns the identity, so all table
generators are proper curve points.
-/
structure Generators where
  S : ℕ → SWPoint Pallas.curve
  S_ne_zero : ∀ k < 2 ^ K, S k ≠ 0

namespace Generators

theorem S_onCurve (G : Generators) {k : ℕ} (hk : k < 2 ^ K) :
    Pallas.OnCurve ((G.S k).x, (G.S k).y) :=
  SWPoint.onCurve_of_ne_zero (G.S_ne_zero k hk)

end Generators

/-! ### Chain lemmas -/

theorem hashToPoint_nil (S : ℕ → SWPoint Pallas.curve) (Q : SWPoint Pallas.curve) :
    hashToPoint S Q [] = some Q := rfl

private theorem foldl_none (S : ℕ → SWPoint Pallas.curve) (ms : List ℕ) :
    ms.foldl (fun acc m => acc.bind (step S · m)) none = none := by
  induction ms with
  | nil => rfl
  | cons m ms ih => exact ih

theorem hashToPoint_cons (S : ℕ → SWPoint Pallas.curve) (Q : SWPoint Pallas.curve)
    (m : ℕ) (ms : List ℕ) :
    hashToPoint S Q (m :: ms)
      = (step S Q m).bind fun acc => hashToPoint S acc ms := by
  show List.foldl _ (step S Q m) ms = _
  cases h : step S Q m with
  | none =>
    show List.foldl _ none ms = none
    exact foldl_none S ms
  | some acc =>
    rfl

theorem hashToPoint_append (S : ℕ → SWPoint Pallas.curve) (Q : SWPoint Pallas.curve)
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
theorem step_ne_zero {S : ℕ → SWPoint Pallas.curve} {A B : SWPoint Pallas.curve}
    {m : ℕ} (h : step S A m = some B) : B ≠ 0 := by
  unfold step at h
  by_cases hc₁ : A = 0 ∨ S m = 0 ∨ A.x = (S m).x
  · rw [incompleteAdd, if_pos hc₁] at h
    simp at h
  rw [incompleteAdd, if_neg hc₁] at h
  rw [show ((some (A + S m)).bind fun t => incompleteAdd t A)
    = incompleteAdd (A + S m) A from rfl] at h
  by_cases hc₂ : A + S m = 0 ∨ A = 0 ∨ (A + S m).x = A.x
  · rw [incompleteAdd, if_pos hc₂] at h
    simp at h
  rw [incompleteAdd, if_neg hc₂] at h
  push_neg at hc₂
  obtain rfl : A + S m + A = B := Option.some.inj h
  intro h0
  exact hc₂.2.2 (by rw [add_eq_zero_iff_eq_neg.mp h0, SWPoint.neg_x])

/-- Chain points of a defined hash are never the identity. -/
theorem hashToPoint_ne_zero {S : ℕ → SWPoint Pallas.curve} {Q B : SWPoint Pallas.curve}
    {l : List ℕ} (hQ : Q ≠ 0) (h : hashToPoint S Q l = some B) : B ≠ 0 := by
  induction l generalizing Q with
  | nil =>
    rw [hashToPoint_nil] at h
    exact Option.some.inj h ▸ hQ
  | cons m ms ih =>
    rw [hashToPoint_cons] at h
    cases hs : step S Q m with
    | none =>
      rw [hs] at h
      simp at h
    | some C =>
      rw [hs] at h
      exact ih (step_ne_zero hs) h

/-- Split a defined chain at a list boundary. -/
theorem hashToPoint_append_some {S : ℕ → SWPoint Pallas.curve}
    {Q B : SWPoint Pallas.curve} {l₁ l₂ : List ℕ}
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
theorem hashToPoint_concat (S : ℕ → SWPoint Pallas.curve) (Q : SWPoint Pallas.curve)
    (l : List ℕ) (m : ℕ) :
    hashToPoint S Q (l ++ [m])
      = (hashToPoint S Q l).bind fun acc => step S acc m := by
  rw [hashToPoint_append]
  cases h : hashToPoint S Q l with
  | none => rfl
  | some acc =>
    show hashToPoint S acc [m] = step S acc m
    rw [hashToPoint_cons]
    cases h : step S acc m with
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
def noteCommitChunks (gdX gdY pkdX pkdY v rho psi : ℕ) : List ℕ :=
  let msg := gdX + 2 ^ 255 * gdY + 2 ^ 256 * pkdX + 2 ^ 511 * pkdY
    + 2 ^ 512 * v + 2 ^ 576 * rho + 2 ^ 831 * psi
  (List.range 109).map fun i => msg / 2 ^ (K * i) % 2 ^ K

end Orchard.Specs.Sinsemilla
