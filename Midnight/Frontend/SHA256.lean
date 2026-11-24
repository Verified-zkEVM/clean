import Midnight.Frontend.Native
import Midnight.SHA256.InnerProducts

/-! Source port at midnight-zk 1e39c120d05200373285fba0e69766e40292b470:
`zk_stdlib/src/lib.rs::ZkStdLib::configure`, default architecture plus sha2_256, and
`circuits/src/hash/sha256/sha256_chip.rs::configure`. Query calls follow Rust let order,
including calls whose first occurrence does not follow polynomial traversal order. The
"11-11-10 decomposition" is a Clean `Gate.withSelector` gate going through `createGate`. -/
namespace Midnight.Frontend.SHA256
open scoped Halo2.ElaboratedConfigure
open Halo2 (Column Selector Gate queryAdvice)
open Keygen (E)
open Midnight.SHA256 (pow2ip pow4ip sumExpr)

/-- Rust's "11-11-10 decomposition", with `pow2ip [21, 10, 0]` written out for `selector_free`. -/
def decompositionGate (q : Selector) (plain output : Column .advice) : Gate F :=
  let p11a : E := queryAdvice plain (-1)
  let p11b : E := queryAdvice plain 0
  let p_10 : E := queryAdvice plain 1
  let out : E := queryAdvice output (-1)
  Halo2.Gate.withSelector "11-11-10 decomposition" q [p11a, p11b, p_10, out]
    [("11-11-10 decomposition",
      (.const ((2 : F) ^ 21) : E) * p11a + (.const ((2 : F) ^ 10) : E) * p11b + p_10 - out)]

def shaConfigure (sharedAdvice : Array (Column .advice)) (sharedFixed : Array (Column .fixed)) :
    Configure Unit := do
  let advice_cols := #[6, 0, 7, 1, 2, 3, 4, 5].map fun i => sharedAdvice[i]!
  let ac : Nat → Column .advice := fun i => advice_cols[i]!
  for i in [:advice_cols.size] do
    if i != 0 && i != 2 then enableEquality (ac i)
  let q_lookup ← complexSelector
  let nbits_col ← lookupTableColumn
  let plain_col ← lookupTableColumn
  let sprdd_col ← lookupTableColumn
  let q_maj ← selector
  let q_half_ch ← selector
  let q_Sigma_0 ← selector
  let q_Sigma_1 ← selector
  let q_sigma_0 ← selector
  let q_sigma_1 ← selector
  let q_11_11_10 ← selector
  let q_10_9_11_2 ← selector
  let q_7_12_2_5_6 ← selector
  let q_12_1x3_7_3_4_3 ← selector
  let q_add_mod_2_32 ← selector
  batchedLookup "plain-spreaded lookup" (some q_lookup) do
    let nbits_0 ← fixed sharedFixed[0]!
    let nbits_1 ← fixed sharedFixed[1]!
    let plain_0 ← advice (ac 0)
    let plain_1 ← advice (ac 2)
    let sprdd_0 ← advice (ac 1)
    let sprdd_1 ← advice (ac 3)
    return #[(#[nbits_0, nbits_1], nbits_col), (#[plain_0, plain_1], plain_col),
      (#[sprdd_0, sprdd_1], sprdd_col)]

  gate "Maj(A, B, C)" q_maj do
    let sA ← advice (ac 5) (-1)
    let sB ← advice (ac 6) (-1)
    let sC ← advice (ac 5) (0)
    let s_odd_11a ← advice (ac 1) (-1)
    let s_odd_11b ← advice (ac 1) (0)
    let s_odd_010 ← advice (ac 1) (1)
    let s_evn_11a ← advice (ac 3) (-1)
    let s_evn_11b ← advice (ac 3) (0)
    let s_evn_010 ← advice (ac 3) (1)
    let s_evn := pow4ip [21, 10, 0] [s_evn_11a, s_evn_11b, s_evn_010]
    let s_odd := pow4ip [21, 10, 0] [s_odd_11a, s_odd_11b, s_odd_010]
    let id := (sA + sB + sC) - (s_evn + (.const 2 : E) * s_odd)
    return #[("Maj", id)]
  gate "half Ch(E, F, G)" q_half_ch do
    let sX ← advice (ac 5) (-1)
    let sY ← advice (ac 6) (-1)
    let s_odd_11a ← advice (ac 1) (-1)
    let s_odd_11b ← advice (ac 1) (0)
    let s_odd_010 ← advice (ac 1) (1)
    let s_evn_11a ← advice (ac 3) (-1)
    let s_evn_11b ← advice (ac 3) (0)
    let s_evn_010 ← advice (ac 3) (1)
    let summand_1 ← advice (ac 4) (0)
    let summand_2 ← advice (ac 5) (0)
    let sum ← advice (ac 6) (0)
    let s_evn := pow4ip [21, 10, 0] [s_evn_11a, s_evn_11b, s_evn_010]
    let s_odd := pow4ip [21, 10, 0] [s_odd_11a, s_odd_11b, s_odd_010]
    let sprdd_id := (sX + sY) - (s_evn + (.const 2 : E) * s_odd)
    let sum_id := (summand_1 + summand_2) - sum
    return #[("Half-Ch spreadded", sprdd_id), ("Half Ch sum (2 terms)", sum_id)]
  gate "Σ₀(A)" q_Sigma_0 do
    let s10 ← advice (ac 5) (-1)
    let s09 ← advice (ac 6) (-1)
    let s11 ← advice (ac 5) (0)
    let s02 ← advice (ac 6) (0)
    let s_evn_11a ← advice (ac 1) (-1)
    let s_evn_11b ← advice (ac 1) (0)
    let s_evn_010 ← advice (ac 1) (1)
    let s_odd_11a ← advice (ac 3) (-1)
    let s_odd_11b ← advice (ac 3) (0)
    let s_odd_010 ← advice (ac 3) (1)
    let s_1st_rot := pow4ip [30, 20, 11, 0] [s02, s10, s09, s11]
    let s_2nd_rot := pow4ip [21, 19, 9, 0] [s11, s02, s10, s09]
    let s_3rd_rot := pow4ip [23, 12, 10, 0] [s09, s11, s02, s10]
    let s_evn := pow4ip [21, 10, 0] [s_evn_11a, s_evn_11b, s_evn_010]
    let s_odd := pow4ip [21, 10, 0] [s_odd_11a, s_odd_11b, s_odd_010]
    let id := (s_1st_rot + s_2nd_rot + s_3rd_rot) - (s_evn + (.const 2 : E) * s_odd)
    return #[("Sigma_0", id)]
  gate "Σ₁(E)" q_Sigma_1 do
    let s07 ← advice (ac 5) (-1)
    let s12 ← advice (ac 6) (-1)
    let s02 ← advice (ac 5) (0)
    let s05 ← advice (ac 6) (0)
    let s06 ← advice (ac 5) (1)
    let s_evn_11a ← advice (ac 1) (-1)
    let s_evn_11b ← advice (ac 1) (0)
    let s_evn_10 ← advice (ac 1) (1)
    let s_odd_11a ← advice (ac 3) (-1)
    let s_odd_11b ← advice (ac 3) (0)
    let s_odd_10 ← advice (ac 3) (1)
    let s_1st_rot := pow4ip [26, 19, 7, 5, 0] [s06, s07, s12, s02, s05]
    let s_2nd_rot := pow4ip [27, 21, 14, 2, 0] [s05, s06, s07, s12, s02]
    let s_3rd_rot := pow4ip [20, 18, 13, 7, 0] [s12, s02, s05, s06, s07]
    let s_evn := pow4ip [21, 10, 0] [s_evn_11a, s_evn_11b, s_evn_10]
    let s_odd := pow4ip [21, 10, 0] [s_odd_11a, s_odd_11b, s_odd_10]
    let id := (s_1st_rot + s_2nd_rot + s_3rd_rot) - (s_evn + (.const 2 : E) * s_odd)
    return #[("Sigma_1", id)]
  gate "σ₀(W)" q_sigma_0 do
    let s12 ← advice (ac 5) (-1)
    let s1a ← advice (ac 6) (-1)
    let s1b ← advice (ac 4) (0)
    let s1c ← advice (ac 5) (0)
    let s07 ← advice (ac 6) (0)
    let s3a ← advice (ac 4) (1)
    let s04 ← advice (ac 5) (1)
    let s3b ← advice (ac 6) (1)
    let s_evn_11a ← advice (ac 1) (-1)
    let s_evn_11b ← advice (ac 1) (0)
    let s_evn_10 ← advice (ac 1) (1)
    let s_odd_11a ← advice (ac 3) (-1)
    let s_odd_11b ← advice (ac 3) (0)
    let s_odd_10 ← advice (ac 3) (1)
    let sprdd_1st_shift := pow4ip [17, 16, 15, 14, 7, 4, 0] [s12, s1a, s1b, s1c, s07, s3a, s04]
    let sprdd_2nd_rot := pow4ip [28, 25, 13, 12, 11, 10, 3, 0]
      [s04, s3b, s12, s1a, s1b, s1c, s07, s3a]
    let sprdd_3rd_rot := pow4ip [31, 24, 21, 17, 14, 2, 1, 0]
      [s1c, s07, s3a, s04, s3b, s12, s1a, s1b]
    let sprdd_evn := pow4ip [21, 10, 0] [s_evn_11a, s_evn_11b, s_evn_10]
    let sprdd_odd := pow4ip [21, 10, 0] [s_odd_11a, s_odd_11b, s_odd_10]
    let id := (sprdd_1st_shift + sprdd_2nd_rot + sprdd_3rd_rot) -
      (sprdd_evn + (.const 2 : E) * sprdd_odd)
    return #[("sigma_0", id)]
  gate "σ₁(W)" q_sigma_1 do
    let s12 ← advice (ac 5) (-1)
    let s1a ← advice (ac 6) (-1)
    let s1b ← advice (ac 4) (0)
    let s1c ← advice (ac 5) (0)
    let s07 ← advice (ac 6) (0)
    let s3a ← advice (ac 4) (1)
    let s04 ← advice (ac 5) (1)
    let s3b ← advice (ac 6) (1)
    let s_evn_11a ← advice (ac 1) (-1)
    let s_evn_11b ← advice (ac 1) (0)
    let s_evn_10 ← advice (ac 1) (1)
    let s_odd_11a ← advice (ac 3) (-1)
    let s_odd_11b ← advice (ac 3) (0)
    let s_odd_10 ← advice (ac 3) (1)
    let sprdd_1st_shift := pow4ip [10, 9, 8, 7, 0] [s12, s1a, s1b, s1c, s07]
    let sprdd_2nd_rot := pow4ip [25, 22, 18, 15, 3, 2, 1, 0]
      [s07, s3a, s04, s3b, s12, s1a, s1b, s1c]
    let sprdd_3rd_rot := pow4ip [31, 30, 23, 20, 16, 13, 1, 0]
      [s1b, s1c, s07, s3a, s04, s3b, s12, s1a]
    let sprdd_evn := pow4ip [21, 10, 0] [s_evn_11a, s_evn_11b, s_evn_10]
    let sprdd_odd := pow4ip [21, 10, 0] [s_odd_11a, s_odd_11b, s_odd_10]
    let id := (sprdd_1st_shift + sprdd_2nd_rot + sprdd_3rd_rot) -
      (sprdd_evn + (.const 2 : E) * sprdd_odd)
    return #[("sigma_1", id)]
  createGate (decompositionGate q_11_11_10 (ac 0) (ac 4))
  gate "10-9-11-2 decomposition" q_10_9_11_2 do
    let p10 ← advice (ac 0) (-1)
    let p09 ← advice (ac 2) (-1)
    let p11 ← advice (ac 0) (0)
    let p02 ← advice (ac 2) (0)
    let s10 ← advice (ac 1) (-1)
    let s09 ← advice (ac 3) (-1)
    let s11 ← advice (ac 1) (0)
    let s02 ← advice (ac 3) (0)
    let plain ← advice (ac 4) (-1)
    let sprdd ← advice (ac 4) (0)
    let plain_id := pow2ip [22, 13, 2, 0] [p10, p09, p11, p02] - plain
    let sprdd_id := pow4ip [22, 13, 2, 0] [s10, s09, s11, s02] - sprdd
    return #[("10_9_11_2 decomposition plain", plain_id),
      ("10_9_11_2 decomposition sprdd", sprdd_id)]
  gate "7-12-2-5-6 decomposition" q_7_12_2_5_6 do
    let p07 ← advice (ac 0) (-1)
    let p12 ← advice (ac 2) (-1)
    let p02 ← advice (ac 0) (0)
    let p05 ← advice (ac 2) (0)
    let p06 ← advice (ac 0) (1)
    let s07 ← advice (ac 1) (-1)
    let s12 ← advice (ac 3) (-1)
    let s02 ← advice (ac 1) (0)
    let s05 ← advice (ac 3) (0)
    let s06 ← advice (ac 1) (1)
    let plain ← advice (ac 4) (-1)
    let sprdd ← advice (ac 4) (0)
    let plain_id := pow2ip [25, 13, 11, 6, 0] [p07, p12, p02, p05, p06] - plain
    let sprdd_id := pow4ip [25, 13, 11, 6, 0] [s07, s12, s02, s05, s06] - sprdd
    return #[("7_12_2_5_6 decomposition plain", plain_id),
      ("7_12_2_5_6 decomposition sprdd", sprdd_id)]
  gate "12-1x3-7-3-4-3 decomposition" q_12_1x3_7_3_4_3 do
    let w12 ← advice (ac 0) (-1)
    let w07 ← advice (ac 2) (-1)
    let w3a ← advice (ac 0) (0)
    let w04 ← advice (ac 2) (0)
    let w3b ← advice (ac 0) (1)
    let w1a ← advice (ac 7) (-1)
    let w1b ← advice (ac 7) (0)
    let w1c ← advice (ac 7) (1)
    let plain ← advice (ac 4) (-1)
    let plain_id := pow2ip [20, 19, 18, 17, 10, 7, 3, 0]
      [w12, w1a, w1b, w1c, w07, w3a, w04, w3b] - plain
    let w_1a_check := w1a * (w1a - (.const 1 : E))
    let w_1b_check := w1b * (w1b - (.const 1 : E))
    let w_1c_check := w1c * (w1c - (.const 1 : E))
    return #[("12_1x3_7_3_4_3 decomposition ", plain_id),
      ("W.1a 1-bit check", w_1a_check),
      ("W.1b 1-bit check", w_1b_check),
      ("W.1c 1-bit check", w_1c_check)]
  gate "add mod 2^32" q_add_mod_2_32 do
    let s0 ← advice (ac 5) (-1)
    let s1 ← advice (ac 6) (-1)
    let s2 ← advice (ac 5) (0)
    let s3 ← advice (ac 6) (0)
    let s4 ← advice (ac 4) (1)
    let s5 ← advice (ac 5) (1)
    let s6 ← advice (ac 6) (1)
    let carry ← advice (ac 2) (1)
    let result ← advice (ac 4) (-1)
    let summands := [s0, s1, s2, s3, s4, s5, s6]
    let lhs := sumExpr summands
    let rhs := result + carry.mulConstant (2 ^ 32)
    return #[("add_mod_2_32", lhs - rhs)]

/-- `nb_arith_cols = 5`, `nr_pow2range_cols = 1`, SHA256 enabled; other optional
chips disabled. The shared resource maxima are 8 advice and 9 fixed columns. -/
def configure : Configure Unit := do
  let advice_columns ← (Array.range 8).mapM fun _ => adviceColumn
  let fixed_columns ← (Array.range (5 + 4)).mapM fun _ => fixedColumn
  let committed_instance_column ← instanceColumn
  let instance_column ← instanceColumn
  nativeConfigure (advice_columns.extract 0 5) fixed_columns
    #[committed_instance_column, instance_column]
  rangeConfigure (advice_columns.extract 1 2)
  -- P2RDecompositionChip::configure merely packages its two existing configs.
  shaConfigure advice_columns (fixed_columns.extract 0 2)

/-- Metadata only, never run: compiling the elaborated term exceeds the heartbeat limit. -/
noncomputable instance (sharedAdvice : Array (Column .advice))
    (sharedFixed : Array (Column .fixed)) :
    Halo2.ElaboratedConfigure (shaConfigure sharedAdvice sharedFixed) := by
  unfold shaConfigure
  try dsimp only
  elaborate_configure

noncomputable instance : Halo2.ElaboratedConfigure configure := by
  unfold configure
  elaborate_configure

end Midnight.Frontend.SHA256
