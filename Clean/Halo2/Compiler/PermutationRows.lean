import Clean.Utils.FieldDomainParams
import Clean.Halo2.Compiler.CopyLayout
import Clean.Halo2.TopLevel

/-! # Compiled permutation-column rows

The compiler resolves copies, builds their array permutation, and labels each image
cell with its column coset and domain row. Keygen commits these row vectors.
-/

variable {F : Type} [FiniteField F]

namespace Halo2.Layout

/-- `[ω^0, ω^1, …, ω^(n−1)]` (`build_vk`'s `omega_powers`, `permutation/keygen.rs:108-116`;
map form rather than iterated multiplication so entries are `getElem`-transparent for the
σ-row identification — the entries use binary exponentiation). -/
def omegaPowersArr (omega : F) (n : ℕ) : Array F :=
  (Array.range n).map (omega ^ ·)

/-- `[δ^0, δ^1, …, δ^(m−1)]` (`build_vk`'s `cur *= DELTA`, `permutation/keygen.rs:118-133`;
map form, see `omegaPowersArr`). -/
def deltaPowersArr (delta : F) (m : ℕ) : Array F :=
  (Array.range m).map (delta ^ ·)

/-- In-range lookup returns the corresponding power of `omega`. -/
theorem omegaPowersArr_getElem! (omega : F) {n j : ℕ} (hj : j < n) :
    (omegaPowersArr omega n)[j]! = omega ^ j := by
  simp [omegaPowersArr, hj]

/-- In-range lookup returns the corresponding power of `delta`. -/
theorem deltaPowersArr_getElem! (delta : F) {m j : ℕ} (hj : j < m) :
    (deltaPowersArr delta m)[j]! = delta ^ j := by
  simp [deltaPowersArr, hj]

variable [FieldDomainParams F]

/-- The per-column permutation polynomials in Lagrange form:
`p_i[j] = deltaomega[i'][j'] = δ^{i'} · ω^{j'}` where `(i', j') = mapping[i][j]`
(`build_vk`, `permutation/keygen.rs:135-146`), over the keygen `Assembly` mapping
(`Assembly::copy` replay, `runAssembly`) of the derived V1 copy list. -/
def permutationRows (k : ℕ) (cs : ConstraintSystem F) (ops : Operations F) :
    List (List F) :=
  let n := 2 ^ k
  let permCols := permColsOf cs
  let copyList := V1.copyList permCols (FloorPlanner.V1.starts ops) ops
    (constantCopyEntries cs ops)
  let mapping := runAssembly n permCols.length copyList
  let omegaPows := omegaPowersArr (FieldDomainParams.omega k) n
  let deltaPows := deltaPowersArr FieldDomainParams.delta permCols.length
  (List.range permCols.length).map fun i =>
    (List.range n).map fun j =>
      let pij := (mapping[i]!)[j]!
      deltaPows[pij.1]! * omegaPows[pij.2]!

/-- Every permutation polynomial is a full-domain row vector. -/
theorem permutationRows_mem_length (k : ℕ) (cs : ConstraintSystem F) (ops : Operations F) :
    ∀ l ∈ permutationRows k cs ops, l.length = 2 ^ k := by
  intro l hl
  simp only [permutationRows, List.mem_map] at hl
  obtain ⟨i, -, rfl⟩ := hl
  simp

theorem permutationRows_length (k : ℕ) (cs : ConstraintSystem F)
    (ops : Operations F) :
    (permutationRows k cs ops).length = (permColsOf cs).length := by
  simp [permutationRows]

theorem permutationRows_getD_length (k : ℕ) (cs : ConstraintSystem F)
    (ops : Operations F) (c : ℕ) (hc : c < (permColsOf cs).length) :
    ((permutationRows k cs ops).getD c []).length = 2 ^ k := by
  have hcl : c < (permutationRows k cs ops).length := by
    rw [permutationRows_length]; exact hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl]
  simp [permutationRows]

end Halo2.Layout

namespace Halo2.TopLevelCircuit

/-- Compiler-generated σ rows, indexed by the global permutation column. -/
def permutationRows [FieldDomainParams F] {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]
    (column : ℕ) : List F :=
  (Layout.permutationRows top.domainExponent top.constraintSystem top.operations).getD column []

end Halo2.TopLevelCircuit
