import Clean.Halo2
import Clean.Ironwood.Ecc.Basic
import Clean.Orchard.Specs.Pallas

/-!
Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/commit_ivk.rs`
- `CommitIvkChip::configure` (lines 60-235): the single two-row
  `"CommitIvk canonicity check"` gate over `advices[0..9]`, gated by `q_commit_ivk`:
  the `b`/`d` subpiece decompositions with `b_1`/`d_1` booleanity, the `ak`/`nk`
  decompositions, and the `b_1 = 1`- / `d_1 = 1`-gated canonicity zeros with the
  `a'`/`b2_c'` shifts — fourteen constraints in the source's exact order.
-/

namespace Halo2.Ironwood.CommitIvk

open Halo2.Ironwood (Fp)
open Orchard (tP)

/-- Rust `bool_check` (`utilities.rs:141-143`): `v · (1 − v)`. -/
private def boolCheck (v : Expression Fp Query) : Expression Fp Query :=
  v * ((1 : Fp) - v)

/-- Rust `CommitIvkConfig` (`commit_ivk.rs:45-51`). -/
structure Config where
  qCommitIvk : Selector
  advices : Fin 10 → Column .advice

/-- `"CommitIvk canonicity check"` (`commit_ivk.rs:78-232`), fourteen constraints in the
source's exact order. -/
def gate (cfg : Config) : Gate Fp where
  name := "CommitIvk canonicity check"
  selector := cfg.qCommitIvk
  constraints :=
    let ak : Expression Fp Query := queryAdvice (cfg.advices 0) 0
    let nk : Expression Fp Query := queryAdvice (cfg.advices 0) 1
    let a : Expression Fp Query := queryAdvice (cfg.advices 1) 0
    let bWhole : Expression Fp Query := queryAdvice (cfg.advices 2) 0
    let c : Expression Fp Query := queryAdvice (cfg.advices 1) 1
    let dWhole : Expression Fp Query := queryAdvice (cfg.advices 2) 1
    let b0 : Expression Fp Query := queryAdvice (cfg.advices 3) 0
    let b1 : Expression Fp Query := queryAdvice (cfg.advices 4) 0
    let b2 : Expression Fp Query := queryAdvice (cfg.advices 5) 0
    let d0 : Expression Fp Query := queryAdvice (cfg.advices 3) 1
    let d1 : Expression Fp Query := queryAdvice (cfg.advices 4) 1
    let z13A : Expression Fp Query := queryAdvice (cfg.advices 6) 0
    let aPrime : Expression Fp Query := queryAdvice (cfg.advices 7) 0
    let z13APrime : Expression Fp Query := queryAdvice (cfg.advices 8) 0
    let z13C : Expression Fp Query := queryAdvice (cfg.advices 6) 1
    let b2CPrime : Expression Fp Query := queryAdvice (cfg.advices 7) 1
    let z14B2CPrime : Expression Fp Query := queryAdvice (cfg.advices 8) 1
    Constraints.withSelector cfg.qCommitIvk
      [("b1_bool_check", boolCheck b1),
       ("d1_bool_check", boolCheck d1),
       ("b_decomposition_check",
        bWhole - (b0 + b1 * (2 ^ 4 : Fp) + b2 * (2 ^ 5 : Fp))),
       ("d_decomposition_check", dWhole - (d0 + d1 * (2 ^ 9 : Fp))),
       ("ak_decomposition_check",
        a + b0 * (2 ^ 250 : Fp) + b1 * (2 ^ 254 : Fp) - ak),
       ("nk_decomposition_check",
        b2 + c * (2 ^ 5 : Fp) + d0 * (2 ^ 245 : Fp) + d1 * (2 ^ 254 : Fp) - nk),
       ("b0_canon_check", b1 * b0),
       ("z13_a_check", b1 * z13A),
       ("a_prime_check", a + (2 ^ 130 : Fp) - (tP : Fp) - aPrime),
       ("z13_a_prime", b1 * z13APrime),
       ("c0_canon_check", d1 * d0),
       ("z13_c_check", d1 * z13C),
       ("b2_c_prime_check",
        b2 + c * (2 ^ 5 : Fp) + (2 ^ 140 : Fp) - (tP : Fp) - b2CPrime),
       ("z14_b2_c_prime", d1 * z14B2CPrime)]

/-- Rust `CommitIvkChip::configure` (`commit_ivk.rs:60-235`), VK-exact. -/
def configure (advices : Fin 10 → Column .advice) : Configure Fp Config := do
  let qCommitIvk ← selector
  let cfg : Config := { qCommitIvk, advices }
  createGate (gate cfg)
  return cfg

end Halo2.Ironwood.CommitIvk
