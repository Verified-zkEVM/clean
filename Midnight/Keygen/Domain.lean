import Midnight.Field
import CompPoly.Univariate.NTT.Domain
import CompElliptic.Fields.Sqrt

/-! Evaluation domains of the scalar field (CompPoly's `BLS12_381.ScalarField`), and the
`Debug` text of one, which Rust hashes into the key. -/
namespace Midnight.Keygen
open CompPoly.CPolynomial.NTT
open CompElliptic.Fields (iterSq iterSq_spec)

/-- `7 ^ ((r - 1) / 2 ^ 32)`, Rust's `ROOT_OF_UNITY` (7 generates the multiplicative group,
`curves/src/bls12_381/fq.rs`). -/
def rootOfUnity : F :=
  10238227357739495823651030575849232062558860180284477541189508159991286009131

theorem rootOfUnity_primitive : IsPrimitiveRoot rootOfUnity (2 ^ 32) := by
  have order := orderOf_eq_prime_pow (p := 2) (n := 31) (x := rootOfUnity)
    (by rw [← iterSq_spec]; decide) (by rw [← iterSq_spec]; decide)
  exact order ▸ IsPrimitiveRoot.orderOf rootOfUnity

/-- The `2 ^ k`-th root of unity Rust's `EvaluationDomain` uses. -/
def omega (k : Nat) : F := iterSq rootOfUnity (32 - k)

def domain (k : Nat) (hk : k ≤ 32) : Domain F where
  logN := k
  omega := omega k
  primitive := by
    have root := rootOfUnity_primitive.pow_of_dvd (p := 2 ^ (32 - k)) (by positivity)
      (pow_dvd_pow 2 (by omega))
    rwa [Nat.pow_div (by omega) (by norm_num), Nat.sub_sub_self hk, ← iterSq_spec] at root

/-- `7 ^ 2 ^ 32`, the coset generator of permutation columns. -/
def delta : F := iterSq 7 32

/-- `EvaluationDomain::new(cs.degree() as u32, k)`'s `extended_k` (keygen.rs:44, domain.rs:54-67):
the degree is truncated to `u32`. -/
def extendedK (k degree : Nat) : Nat :=
  let j := degree % 2 ^ 32
  if j ≤ 2 then k else k + (j - 2).log2 + 1

/-- Exact Rust `Debug` spelling hashed into the VK transcript. -/
def domainDebug (k degree : Nat) : String :=
  "PinnedEvaluationDomain { k: " ++ toString k ++ ", extended_k: " ++
    toString (extendedK k degree) ++ ", omega: Fq(0x" ++ (BitVec.ofNat 256 (omega k).val).toHex ++
    ") }"

end Midnight.Keygen
