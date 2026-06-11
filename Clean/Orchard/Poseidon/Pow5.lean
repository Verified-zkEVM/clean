import Clean.Circuit
import Clean.Orchard.Ecc
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard Poseidon Pow5 gates and chip entry points

Clean approximations of the Halo2 `Pow5Chip` custom gates used by Orchard's
`P128Pow5T3` nullifier hash.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon/pow5.rs`
- `full round`
- `partial rounds`
- `pad-and-add`

Orchard configures `Pow5Chip<pallas::Base, 3, 2>` in
`orchard@0.14.0/src/circuit.rs`. These assertions specialize the source polynomials to
width 3 and rate 2.
-/

namespace Orchard
namespace Poseidon

variable {F : Type} [Field F]

def pow5 {K : Type} [Mul K] (x : K) : K :=
  let x2 := x * x
  x2 * x2 * x

private theorem eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : b = a := by
  exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)).symm

private theorem left_eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : a = b :=
  (eq_of_add_neg_eq_zero h).symm

namespace FullRound

structure Params (F : Type) where
  rcA0 : F
  rcA1 : F
  rcA2 : F
  m00 : F
  m01 : F
  m02 : F
  m10 : F
  m11 : F
  m12 : F
  m20 : F
  m21 : F
  m22 : F

structure Row (F : Type) where
  cur0 : F
  cur1 : F
  cur2 : F
  next0 : F
  next1 : F
  next2 : F
deriving ProvableStruct

def Params.toExpr (params : Params Ecc.Fp) :
    Params (Expression Ecc.Fp) where
  rcA0 := params.rcA0
  rcA1 := params.rcA1
  rcA2 := params.rcA2
  m00 := params.m00
  m01 := params.m01
  m02 := params.m02
  m10 := params.m10
  m11 := params.m11
  m12 := params.m12
  m20 := params.m20
  m21 := params.m21
  m22 := params.m22

def s0 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  pow5 (row.cur0 + params.rcA0)

def s1 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  pow5 (row.cur1 + params.rcA1)

def s2 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  pow5 (row.cur2 + params.rcA2)

def output0 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  s0 params row * params.m00 + s1 params row * params.m01 + s2 params row * params.m02

def output1 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  s0 params row * params.m10 + s1 params row * params.m11 + s2 params row * params.m12

def output2 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  s0 params row * params.m20 + s1 params row * params.m21 + s2 params row * params.m22

def next0Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  output0 params row - row.next0

def next1Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  output1 params row - row.next1

def next2Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  output2 params row - row.next2

def Spec (params : Params Ecc.Fp) (row : Row Ecc.Fp) : Prop :=
  row.next0 = output0 params row ∧
    row.next1 = output1 params row ∧
    row.next2 = output2 params row

def main (params : Params Ecc.Fp)
    (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  let paramsExpr := params.toExpr
  assertZero (next0Check paramsExpr row)
  assertZero (next1Check paramsExpr row)
  assertZero (next2Check paramsExpr row)

def circuit (params : Params Ecc.Fp) : FormalAssertion Ecc.Fp Row where
  name := "GATE full round"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, next0Check, next1Check, next2Check,
      output0, output1, output2, s0, s1, s2, pow5, Params.toExpr]
    rcases h_holds with ⟨h0, h1, h2⟩
    constructor
    · exact eq_of_add_neg_eq_zero h0
    constructor
    · exact eq_of_add_neg_eq_zero h1
    · exact eq_of_add_neg_eq_zero h2
  completeness := by
    circuit_proof_start [main, Spec, next0Check, next1Check, next2Check,
      output0, output1, output2, s0, s1, s2, pow5, Params.toExpr]
    simp_all
    ring_nf
    simp

end FullRound

namespace PartialRounds

structure Params (F : Type) where
  rcA0 : F
  rcA1 : F
  rcA2 : F
  rcB0 : F
  rcB1 : F
  rcB2 : F
  m00 : F
  m01 : F
  m02 : F
  m10 : F
  m11 : F
  m12 : F
  m20 : F
  m21 : F
  m22 : F
  mInv00 : F
  mInv01 : F
  mInv02 : F
  mInv10 : F
  mInv11 : F
  mInv12 : F
  mInv20 : F
  mInv21 : F
  mInv22 : F

structure Row (F : Type) where
  cur0 : F
  cur1 : F
  cur2 : F
  mid0Sbox : F
  next0 : F
  next1 : F
  next2 : F
deriving ProvableStruct

def Params.toExpr (params : Params Ecc.Fp) :
    Params (Expression Ecc.Fp) where
  rcA0 := params.rcA0
  rcA1 := params.rcA1
  rcA2 := params.rcA2
  rcB0 := params.rcB0
  rcB1 := params.rcB1
  rcB2 := params.rcB2
  m00 := params.m00
  m01 := params.m01
  m02 := params.m02
  m10 := params.m10
  m11 := params.m11
  m12 := params.m12
  m20 := params.m20
  m21 := params.m21
  m22 := params.m22
  mInv00 := params.mInv00
  mInv01 := params.mInv01
  mInv02 := params.mInv02
  mInv10 := params.mInv10
  mInv11 := params.mInv11
  mInv12 := params.mInv12
  mInv20 := params.mInv20
  mInv21 := params.mInv21
  mInv22 := params.mInv22

def mid0Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  pow5 (row.cur0 + params.rcA0) - row.mid0Sbox

def mid0 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  row.mid0Sbox * params.m00 + (row.cur1 + params.rcA1) * params.m01 +
    (row.cur2 + params.rcA2) * params.m02

def mid1 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  row.mid0Sbox * params.m10 + (row.cur1 + params.rcA1) * params.m11 +
    (row.cur2 + params.rcA2) * params.m12

def mid2 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  row.mid0Sbox * params.m20 + (row.cur1 + params.rcA1) * params.m21 +
    (row.cur2 + params.rcA2) * params.m22

def nextInv0 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  row.next0 * params.mInv00 + row.next1 * params.mInv01 + row.next2 * params.mInv02

def nextInv1 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  row.next0 * params.mInv10 + row.next1 * params.mInv11 + row.next2 * params.mInv12

def nextInv2 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  row.next0 * params.mInv20 + row.next1 * params.mInv21 + row.next2 * params.mInv22

def next0Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  pow5 (mid0 params row + params.rcB0) - nextInv0 params row

def next1Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  mid1 params row + params.rcB1 - nextInv1 params row

def next2Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  mid2 params row + params.rcB2 - nextInv2 params row

def Spec (params : Params Ecc.Fp) (row : Row Ecc.Fp) : Prop :=
  row.mid0Sbox = pow5 (row.cur0 + params.rcA0) ∧
    nextInv0 params row = pow5 (mid0 params row + params.rcB0) ∧
    nextInv1 params row = mid1 params row + params.rcB1 ∧
    nextInv2 params row = mid2 params row + params.rcB2

def main (params : Params Ecc.Fp)
    (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  let paramsExpr := params.toExpr
  assertZero (mid0Check paramsExpr row)
  assertZero (next0Check paramsExpr row)
  assertZero (next1Check paramsExpr row)
  assertZero (next2Check paramsExpr row)

def circuit (params : Params Ecc.Fp) : FormalAssertion Ecc.Fp Row where
  name := "GATE partial rounds"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, mid0Check, next0Check, next1Check,
      next2Check, mid0, mid1, mid2, nextInv0, nextInv1, nextInv2, pow5,
      Params.toExpr]
    rcases h_holds with ⟨hmid, h0, h1, h2⟩
    constructor
    · exact eq_of_add_neg_eq_zero hmid
    constructor
    · exact eq_of_add_neg_eq_zero h0
    constructor
    · exact eq_of_add_neg_eq_zero h1
    · exact eq_of_add_neg_eq_zero h2
  completeness := by
    circuit_proof_start [main, Spec, mid0Check, next0Check, next1Check,
      next2Check, mid0, mid1, mid2, nextInv0, nextInv1, nextInv2, pow5,
      Params.toExpr]
    simp_all
    ring_nf
    simp

end PartialRounds

namespace PadAndAdd

structure Row (F : Type) where
  initial0 : F
  initial1 : F
  initial2 : F
  input0 : F
  input1 : F
  output0 : F
  output1 : F
  output2 : F
deriving ProvableStruct

def output0Check {K : Type} [Add K] [Sub K] (row : Row K) : K :=
  row.initial0 + row.input0 - row.output0

def output1Check {K : Type} [Add K] [Sub K] (row : Row K) : K :=
  row.initial1 + row.input1 - row.output1

def capacityCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.initial2 - row.output2

def Spec (row : Row Ecc.Fp) : Prop :=
  row.output0 = row.initial0 + row.input0 ∧
    row.output1 = row.initial1 + row.input1 ∧
    row.output2 = row.initial2

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertZero (output0Check row)
  assertZero (output1Check row)
  assertZero (capacityCheck row)

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE pad-and-add"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, output0Check, output1Check, capacityCheck]
    rcases h_holds with ⟨h0, h1, h2⟩
    constructor
    · have h0' : input_initial0 + input_input0 - input_output0 = 0 := by
        simp_all [sub_eq_add_neg]
      exact (sub_eq_zero.mp h0').symm
    constructor
    · have h1' : input_initial1 + input_input1 - input_output1 = 0 := by
        simp_all [sub_eq_add_neg]
      exact (sub_eq_zero.mp h1').symm
    · have h2' : input_initial2 - input_output2 = 0 := by
        simp_all [sub_eq_add_neg]
      exact (sub_eq_zero.mp h2').symm
  completeness := by
    circuit_proof_start [main, Spec, output0Check, output1Check, capacityCheck]
    simp_all
    constructor <;> ring

end PadAndAdd

namespace Permute

/-!
Source reference: `poseidon/pow5.rs::Pow5Chip::permute` and
`Pow5State::{load,full_round,partial_round,round}`.

For Orchard's `P128Pow5T3`, `WIDTH = 3`, `RATE = 2`, `R_F = 8`, and `R_P = 56`.
Halo2 lays out one full round per row and two partial rounds per row:

- copy/load the incoming state at row 0;
- 4 first-half full-round rows;
- 28 partial-round rows, each representing rounds `r` and `r+1`;
- 4 second-half full-round rows.

The circuit below mirrors that schedule while keeping the actual constants as Lean
parameters.  This is intentionally the `Pow5Chip::permute` surface: callers supply only
an initial state and receive the final state; intermediate rows are witnessed inside the
circuit.
-/

/-- Width-3 Poseidon state used by Orchard's `P128Pow5T3`. -/
structure State (F : Type) where
  x0 : F
  x1 : F
  x2 : F
deriving ProvableStruct

namespace P128Pow5T3
/-- Interpret Halo2 `pallas::Base::from_raw` little-endian 64-bit limbs. -/
def fromRaw (l0 l1 l2 l3 : Nat) : Ecc.Fp :=
  (l0 + 2 ^ 64 * l1 + 2 ^ 128 * l2 + 2 ^ 192 * l3 : Nat)

/-- P128Pow5T3 `MDS` matrix over Pallas base, ported from `halo2_poseidon/src/fp.rs`. -/
def mds : Nat → Nat → Ecc.Fp
  | 0, 0 => fromRaw 3620652786995239779 10941390476615682902 12958439140294781652 771775491557723623
  | 0, 1 => fromRaw 10289130405333740382 2597814459711051574 2972110829885618516 3571748305317288635
  | 0, 2 => fromRaw 1860495882540561501 11575296791174797109 15565448752179597279 558523139050038694
  | 1, 0 => fromRaw 15008753495564424828 4182232445879154442 17933983967831928223 2535916242775023319
  | 1, 1 => fromRaw 4621379386992785966 8716776849784154887 12927130094725535101 2723237799138601136
  | 1, 2 => fromRaw 17892098110593660026 11145632283026774079 8400206265390340439 2519119548415220887
  | 2, 0 => fromRaw 18367836059708218340 2407190131743899997 17524538118055867492 3326433177438457911
  | 2, 1 => fromRaw 14371531744063403620 14693825613060777155 10579340894105704037 2097176931241650056
  | 2, 2 => fromRaw 1541238319548489457 8468786250665046518 5899939721334036153 4321031255276163940
  | _, _ => 0

/-- P128Pow5T3 `MDSINV` matrix over Pallas base, ported from `halo2_poseidon/src/fp.rs`. -/
def mdsInv : Nat → Nat → Ecc.Fp
  | 0, 0 => fromRaw 14329968291362131563 4990956366285343413 14725081725716161603 3224674038581586042
  | 0, 1 => fromRaw 1664150712322061686 18076314957651265430 6906036201411609477 3668116174685169637
  | 0, 2 => fromRaw 10675296646881109216 1442237576821874752 17609487455796105722 3363729294698305897
  | 1, 0 => fromRaw 11658153772397471392 1436776915026414377 15787567157432865389 558224821545496985
  | 1, 1 => fromRaw 16727536405800263769 13483043927481500095 111061169655799213 3092962521913441521
  | 1, 2 => fromRaw 16164574508216092545 8553082345022233398 1303110714430473906 671845740643625712
  | 2, 0 => fromRaw 3044870461749446920 12608127523569523637 8231000811050478374 3444051328397582873
  | 2, 1 => fromRaw 8570256919438797067 14259687304689143095 13032806769834140246 2217801975518692635
  | 2, 2 => fromRaw 12522420651677217518 9774855583763578497 4334426893519794660 940178088060449066
  | _, _ => 0

/-- The explicit P128Pow5T3 matrices satisfy `MDS_INV * MDS = I`. -/
theorem mdsInv_mul_mds (i j : Fin 3) :
    mdsInv i.val 0 * mds 0 j.val + mdsInv i.val 1 * mds 1 j.val +
      mdsInv i.val 2 * mds 2 j.val = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j
  · change ((905457334243774457406483481563174903331369998272502669964302313549729653048815382454531386933288977413134376651702248431747669994576093617278755014122761 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((1 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((1125369057355178362565835492273472726208154592603215705108034755307179642311313632199131204034254268641756658265125610831480272041058530452386248133722878 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((0 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((1007755862194239789516852909801011739078263427832546604307054063048796474120851327601368805426727409225903068132618622361226255214794701761938089228952059 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((0 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((414082306416280423128121979954833554954275063322831905126278252041948615568209596509495319348751535957217423159363288946106819740263944250751302396193504 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((0 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((465955926416090631753147850592035640342151361220113399997543671215509746741994979959193554435612531047340330539485644586093216602700073754508979111947554 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((1 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((433673857820935244456465896065845207296158781552364420302426618874983484272712688267797076528230731483779189870941874500509388498468792026874129403229435 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((0 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((449562471328863485691198914517216279512777148692691056159194856255209126857881222111506772307171593026130668102257869742245989185279168589744409745186660 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((0 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((800357445755740618006025545006491399277586693701757620137578742873681938279368910023526624149639047081708813274879555286061778289746910215341623666466786 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((0 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((456000582988329970701188121217362227123777375892574425683157939357257545157611876874222197847198078100162159365397501348018592369521261023507870991370548 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((1 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

/-- Applying the explicit inverse matrix to `MDS * r` returns `r`. -/
theorem mdsInv_mul_mds_apply (i : Fin 3) (r0 r1 r2 : Ecc.Fp) :
    (r0 * mds 0 0 + r1 * mds 0 1 + r2 * mds 0 2) * mdsInv i.val 0 +
      (r0 * mds 1 0 + r1 * mds 1 1 + r2 * mds 1 2) * mdsInv i.val 1 +
      (r0 * mds 2 0 + r1 * mds 2 1 + r2 * mds 2 2) * mdsInv i.val 2 =
    match i with
    | ⟨0, _⟩ => r0
    | ⟨1, _⟩ => r1
    | _ => r2 := by
  fin_cases i
  · have h00 := mdsInv_mul_mds ⟨0, by norm_num⟩ ⟨0, by norm_num⟩
    have h01 := mdsInv_mul_mds ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
    have h02 := mdsInv_mul_mds ⟨0, by norm_num⟩ ⟨2, by norm_num⟩
    simp at h00 h01 h02
    linear_combination r0 * h00 + r1 * h01 + r2 * h02
  · have h10 := mdsInv_mul_mds ⟨1, by norm_num⟩ ⟨0, by norm_num⟩
    have h11 := mdsInv_mul_mds ⟨1, by norm_num⟩ ⟨1, by norm_num⟩
    have h12 := mdsInv_mul_mds ⟨1, by norm_num⟩ ⟨2, by norm_num⟩
    simp at h10 h11 h12
    linear_combination r0 * h10 + r1 * h11 + r2 * h12
  · have h20 := mdsInv_mul_mds ⟨2, by norm_num⟩ ⟨0, by norm_num⟩
    have h21 := mdsInv_mul_mds ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
    have h22 := mdsInv_mul_mds ⟨2, by norm_num⟩ ⟨2, by norm_num⟩
    simp at h20 h21 h22
    linear_combination r0 * h20 + r1 * h21 + r2 * h22

/-- The explicit P128Pow5T3 matrices also satisfy `MDS * MDS_INV = I`. -/
theorem mds_mul_mdsInv (i j : Fin 3) :
    mds i.val 0 * mdsInv 0 j.val + mds i.val 1 * mdsInv 1 j.val +
      mds i.val 2 * mdsInv 2 j.val = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j
  · change ((252414977221963652040159588858838472674275672223867859224037507807533378360892347491770185987227473984153453302232272321051560602514070509623027844535049 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((1 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((595637745071801538825578886976562432581644860673815276503110093995341293242694362045492894193262535536314223432152895107050083064507232646992077115676495 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((0 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((217531341786394079401826084312512192285910869979333208328170817362611862824639970924504615738262408204698822943055036438887289778195141886775365442250612 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((0 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((723959034974947826707549888555860818275138155216983330064385751646232375073548645886988701046913083082546403953579206285658878342837952018582218493643876 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((0 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((918532324383891622975338057098125967491616155769391793003475552443493351153224249228714657126421740157939297767499982638760507272005172128514725787258468 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((1 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((501514742549093910219214367922196274107711409693404556357747047703746379909533615078807758679232151568580292825802103173657349816069537261968731118865690 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((0 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((1055154691395897133220687357238214748101287033514008102512480712710590474516577573561829630768527065762010498398099131403322639653409048170198115892553556 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((0 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((1113950849104371020328917096715328408984550394751395029376807079754116211609421596209246095727712973214048243646534966077216334084510236197702606993237303 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((0 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  · change ((656466542042339784845321807415608330631406907391930843417490863871470215434305642567462296102450372418544115486853139406047411092278185757157851485647346 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) = ((1 : Nat) : ZMod CompElliptic.Fields.Pasta.PALLAS_BASE_CARD)
    rw [ZMod.natCast_eq_natCast_iff']
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

/-- Applying the explicit MDS matrix to `MDS_INV * n` returns `n`. -/
theorem mds_mul_mdsInv_apply (i : Fin 3) (n0 n1 n2 : Ecc.Fp) :
    (n0 * mdsInv 0 0 + n1 * mdsInv 0 1 + n2 * mdsInv 0 2) * mds i.val 0 +
      (n0 * mdsInv 1 0 + n1 * mdsInv 1 1 + n2 * mdsInv 1 2) * mds i.val 1 +
      (n0 * mdsInv 2 0 + n1 * mdsInv 2 1 + n2 * mdsInv 2 2) * mds i.val 2 =
    match i with
    | ⟨0, _⟩ => n0
    | ⟨1, _⟩ => n1
    | _ => n2 := by
  fin_cases i
  · have h00 := mds_mul_mdsInv ⟨0, by norm_num⟩ ⟨0, by norm_num⟩
    have h01 := mds_mul_mdsInv ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
    have h02 := mds_mul_mdsInv ⟨0, by norm_num⟩ ⟨2, by norm_num⟩
    simp at h00 h01 h02
    linear_combination n0 * h00 + n1 * h01 + n2 * h02
  · have h10 := mds_mul_mdsInv ⟨1, by norm_num⟩ ⟨0, by norm_num⟩
    have h11 := mds_mul_mdsInv ⟨1, by norm_num⟩ ⟨1, by norm_num⟩
    have h12 := mds_mul_mdsInv ⟨1, by norm_num⟩ ⟨2, by norm_num⟩
    simp at h10 h11 h12
    linear_combination n0 * h10 + n1 * h11 + n2 * h12
  · have h20 := mds_mul_mdsInv ⟨2, by norm_num⟩ ⟨0, by norm_num⟩
    have h21 := mds_mul_mdsInv ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
    have h22 := mds_mul_mdsInv ⟨2, by norm_num⟩ ⟨2, by norm_num⟩
    simp at h20 h21 h22
    linear_combination n0 * h20 + n1 * h21 + n2 * h22

end P128Pow5T3

/-- Constants needed by one width-3 full round. -/
def fullParams (roundConstants : Nat → State Ecc.Fp) (mds : Nat → Nat → Ecc.Fp)
    (round : Nat) : FullRound.Params Ecc.Fp where
  rcA0 := (roundConstants round).x0
  rcA1 := (roundConstants round).x1
  rcA2 := (roundConstants round).x2
  m00 := mds 0 0
  m01 := mds 0 1
  m02 := mds 0 2
  m10 := mds 1 0
  m11 := mds 1 1
  m12 := mds 1 2
  m20 := mds 2 0
  m21 := mds 2 1
  m22 := mds 2 2

/-- Constants needed by one width-3 partial-round row, which checks two source rounds. -/
def partialParams (roundConstants : Nat → State Ecc.Fp) (mds mdsInv : Nat → Nat → Ecc.Fp)
    (round : Nat) : PartialRounds.Params Ecc.Fp where
  rcA0 := (roundConstants round).x0
  rcA1 := (roundConstants round).x1
  rcA2 := (roundConstants round).x2
  rcB0 := (roundConstants (round + 1)).x0
  rcB1 := (roundConstants (round + 1)).x1
  rcB2 := (roundConstants (round + 1)).x2
  m00 := mds 0 0
  m01 := mds 0 1
  m02 := mds 0 2
  m10 := mds 1 0
  m11 := mds 1 1
  m12 := mds 1 2
  m20 := mds 2 0
  m21 := mds 2 1
  m22 := mds 2 2
  mInv00 := mdsInv 0 0
  mInv01 := mdsInv 0 1
  mInv02 := mdsInv 0 2
  mInv10 := mdsInv 1 0
  mInv11 := mdsInv 1 1
  mInv12 := mdsInv 1 2
  mInv20 := mdsInv 2 0
  mInv21 := mdsInv 2 1
  mInv22 := mdsInv 2 2

/-- P128Pow5T3 partial-round-row parameters for a source round index. -/
def partialParamsP128 (roundConstants : Nat → State Ecc.Fp) (round : Nat) :
    PartialRounds.Params Ecc.Fp :=
  partialParams roundConstants P128Pow5T3.mds P128Pow5T3.mdsInv round

/-- Value-level full-round transition, matching `Pow5State::full_round`. -/
def fullRoundValue (params : FullRound.Params Ecc.Fp) (state : State Ecc.Fp) : State Ecc.Fp :=
  let row : FullRound.Row Ecc.Fp :=
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      next0 := 0, next1 := 0, next2 := 0 }
  { x0 := FullRound.output0 params row
    x1 := FullRound.output1 params row
    x2 := FullRound.output2 params row }

/-- The first-round S-box value witnessed in a partial-round row. -/
def partialMid0SboxValue (params : PartialRounds.Params Ecc.Fp) (state : State Ecc.Fp) : Ecc.Fp :=
  pow5 (state.x0 + params.rcA0)

/-- Value-level partial-round-row transition, matching `Pow5State::partial_round`. -/
def partialRoundValue (params : PartialRounds.Params Ecc.Fp) (state : State Ecc.Fp) : State Ecc.Fp :=
  let rowWithMid : PartialRounds.Row Ecc.Fp :=
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      mid0Sbox := partialMid0SboxValue params state,
      next0 := 0, next1 := 0, next2 := 0 }
  let r0 := pow5 (PartialRounds.mid0 params rowWithMid + params.rcB0)
  let r1 := PartialRounds.mid1 params rowWithMid + params.rcB1
  let r2 := PartialRounds.mid2 params rowWithMid + params.rcB2
  { x0 := r0 * params.m00 + r1 * params.m01 + r2 * params.m02
    x1 := r0 * params.m10 + r1 * params.m11 + r2 * params.m12
    x2 := r0 * params.m20 + r1 * params.m21 + r2 * params.m22 }

/-- The concrete row witnessed by the honest P128 partial-round prover. -/
def partialRowValueP128 (roundConstants : Nat → State Ecc.Fp) (round : Nat)
    (state : State Ecc.Fp) : PartialRounds.Row Ecc.Fp :=
  let params := partialParamsP128 roundConstants round
  let next := partialRoundValue params state
  { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
    mid0Sbox := partialMid0SboxValue params state,
    next0 := next.x0, next1 := next.x1, next2 := next.x2 }

/-- The honest P128 partial-round row satisfies the Halo2 gate relation. -/
theorem partialRowValueP128_spec (roundConstants : Nat → State Ecc.Fp) (round : Nat)
    (state : State Ecc.Fp) :
    PartialRounds.Spec (partialParamsP128 roundConstants round)
      (partialRowValueP128 roundConstants round state) := by
  constructor
  · rfl
  constructor
  · simp [partialRowValueP128, partialRoundValue, partialMid0SboxValue,
      partialParamsP128, partialParams, PartialRounds.nextInv0, PartialRounds.mid0,
      PartialRounds.mid1, PartialRounds.mid2]
    exact P128Pow5T3.mdsInv_mul_mds_apply ⟨0, by norm_num⟩
      (pow5 (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 0 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 0 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 0 2 +
        (roundConstants (round + 1)).x0))
      (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 1 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 1 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 1 2 +
        (roundConstants (round + 1)).x1)
      (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 2 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 2 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 2 2 +
        (roundConstants (round + 1)).x2)
  constructor
  · simp [partialRowValueP128, partialRoundValue, partialMid0SboxValue,
      partialParamsP128, partialParams, PartialRounds.nextInv1, PartialRounds.mid0,
      PartialRounds.mid1, PartialRounds.mid2]
    exact P128Pow5T3.mdsInv_mul_mds_apply ⟨1, by norm_num⟩
      (pow5 (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 0 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 0 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 0 2 +
        (roundConstants (round + 1)).x0))
      (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 1 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 1 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 1 2 +
        (roundConstants (round + 1)).x1)
      (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 2 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 2 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 2 2 +
        (roundConstants (round + 1)).x2)
  · simp [partialRowValueP128, partialRoundValue, partialMid0SboxValue,
      partialParamsP128, partialParams, PartialRounds.nextInv2, PartialRounds.mid0,
      PartialRounds.mid1, PartialRounds.mid2]
    exact P128Pow5T3.mdsInv_mul_mds_apply ⟨2, by norm_num⟩
      (pow5 (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 0 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 0 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 0 2 +
        (roundConstants (round + 1)).x0))
      (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 1 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 1 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 1 2 +
        (roundConstants (round + 1)).x1)
      (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 2 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 2 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 2 2 +
        (roundConstants (round + 1)).x2)

/-! ### Plain Lean permutation specification -/

/-- Apply the four consecutive value-level full rounds used by `Pow5Chip::permute`,
starting at source round `round`. -/
def fullRounds4Value (roundConstants : Nat → State Ecc.Fp) (mds : Nat → Nat → Ecc.Fp)
    (round : Nat) (state : State Ecc.Fp) : State Ecc.Fp :=
  Fin.foldl 4
    (fun state i => fullRoundValue (fullParams roundConstants mds (round + i.val)) state)
    state

/-- Apply the 28 consecutive P128Pow5T3 value-level partial-round rows used by
`Pow5Chip::permute`, starting at source round 4. -/
def partialRoundRows28P128Value (roundConstants : Nat → State Ecc.Fp)
    (state : State Ecc.Fp) : State Ecc.Fp :=
  Fin.foldl 28
    (fun state i =>
      partialRoundValue (partialParamsP128 roundConstants (4 + 2 * i.val)) state)
    state

/-- Plain Lean implementation of Orchard's `P128Pow5T3` `Pow5Chip::permute` schedule. -/
def permuteP128Value (roundConstants : Nat → State Ecc.Fp) (input : State Ecc.Fp) :
    State Ecc.Fp :=
  let s := fullRounds4Value roundConstants P128Pow5T3.mds 0 input
  let s := partialRoundRows28P128Value roundConstants s
  fullRounds4Value roundConstants P128Pow5T3.mds (4 + 56) s

/-- Parameterized compatibility wrapper for the old skeleton API, now also using the
fixed 28-row fold shape. -/
def permuteValue (roundConstants : Nat → State Ecc.Fp) (mds mdsInv : Nat → Nat → Ecc.Fp)
    (input : State Ecc.Fp) : State Ecc.Fp :=
  let s := fullRounds4Value roundConstants mds 0 input
  let s := Fin.foldl 28
    (fun state i => partialRoundValue (partialParams roundConstants mds mdsInv (4 + 2 * i.val)) state)
    s
  fullRounds4Value roundConstants mds (4 + 56) s

/-- Source-level permutation spec: the circuit output is the plain Lean permutation. -/
def Spec (roundConstants : Nat → State Ecc.Fp) (mds mdsInv : Nat → Nat → Ecc.Fp)
    (input output : State Ecc.Fp) : Prop :=
  output = permuteValue roundConstants mds mdsInv input

/-! ### Circuit implementation -/

/-- One source-shaped full-round row: witness the next state internally and assert the
`full round` gate. -/
def fullRound (params : FullRound.Params Ecc.Fp) (state : Var State Ecc.Fp) :
    Circuit Ecc.Fp (Var State Ecc.Fp) := do
  let next ← witness fun env => fullRoundValue params (eval env state)
  FullRound.circuit params
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      next0 := next.x0, next1 := next.x1, next2 := next.x2 }
  return next

/-- Packaged full-round loop body.  This is deliberately a subcircuit even though the
Rust source implements it as a private method, because keeping one row per package makes
loop proofs and elaboration manageable. -/
def fullRoundCircuit (params : FullRound.Params Ecc.Fp) : FormalCircuit Ecc.Fp State State where
  name := "Pow5State::full_round"
  main := fullRound params
  Spec input output := output = fullRoundValue params input
  soundness := by
    circuit_proof_start [fullRound, fullRoundValue, FullRound.circuit, FullRound.Spec,
      FullRound.output0, FullRound.output1, FullRound.output2]
    rcases h_holds with ⟨h0, h1, h2⟩
    simp [State.mk.injEq, FullRound.s0, FullRound.s1, FullRound.s2] at h0 h1 h2 ⊢
    exact ⟨h0, h1, h2⟩
  completeness := by
    circuit_proof_start [fullRound, fullRoundValue, FullRound.circuit, FullRound.Spec,
      FullRound.output0, FullRound.output1, FullRound.output2]
    constructor
    · simpa [FullRound.s0, FullRound.s1, FullRound.s2] using h_env ⟨0, by norm_num⟩
    constructor
    · simpa [FullRound.s0, FullRound.s1, FullRound.s2] using h_env ⟨1, by norm_num⟩
    · simpa [FullRound.s0, FullRound.s1, FullRound.s2] using h_env ⟨2, by norm_num⟩

/-- One source-shaped partial-round row: witness the intermediate S-box and next state
internally and assert the `partial rounds` gate. -/
def partialRound (params : PartialRounds.Params Ecc.Fp) (state : Var State Ecc.Fp) :
    Circuit Ecc.Fp (Var State Ecc.Fp) := do
  let mid0Sbox ← witness fun env => partialMid0SboxValue params (eval env state)
  let next ← witness fun env => partialRoundValue params (eval env state)
  PartialRounds.circuit params
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      mid0Sbox,
      next0 := next.x0, next1 := next.x1, next2 := next.x2 }
  return next

/-- One P128Pow5T3 source-shaped partial-round row. -/
def partialRoundP128 (roundConstants : Nat → State Ecc.Fp) (round : Nat)
    (state : Var State Ecc.Fp) : Circuit Ecc.Fp (Var State Ecc.Fp) :=
  partialRound (partialParamsP128 roundConstants round) state

/-- Packaged P128Pow5T3 partial-round-row loop body. -/
def partialRoundP128Circuit (roundConstants : Nat → State Ecc.Fp) (round : Nat) :
    FormalCircuit Ecc.Fp State State where
  name := "Pow5State::partial_round[P128]"
  main := partialRoundP128 roundConstants round
  Spec input output := output = partialRoundValue (partialParamsP128 roundConstants round) input
  soundness := by
    circuit_proof_start [partialRoundP128, partialRound, partialRoundValue, partialMid0SboxValue,
      PartialRounds.circuit, PartialRounds.Spec, partialParamsP128, partialParams,
      PartialRounds.mid0, PartialRounds.mid1, PartialRounds.mid2,
      PartialRounds.nextInv0, PartialRounds.nextInv1, PartialRounds.nextInv2]
    rcases h_holds with ⟨hmid, h0, h1, h2⟩
    simp [State.mk.injEq] at hmid h0 h1 h2 ⊢
    constructor
    · have happ := P128Pow5T3.mds_mul_mdsInv_apply ⟨0, by norm_num⟩
        (env.get (i₀ + 1)) (env.get (i₀ + 1 + 1)) (env.get (i₀ + 1 + 1 + 1))
      rw [h0, h1, h2] at happ
      simpa [hmid] using happ.symm
    constructor
    · have happ := P128Pow5T3.mds_mul_mdsInv_apply ⟨1, by norm_num⟩
        (env.get (i₀ + 1)) (env.get (i₀ + 1 + 1)) (env.get (i₀ + 1 + 1 + 1))
      rw [h0, h1, h2] at happ
      simpa [hmid] using happ.symm
    · have happ := P128Pow5T3.mds_mul_mdsInv_apply ⟨2, by norm_num⟩
        (env.get (i₀ + 1)) (env.get (i₀ + 1 + 1)) (env.get (i₀ + 1 + 1 + 1))
      rw [h0, h1, h2] at happ
      simpa [hmid] using happ.symm
  completeness := by
    circuit_proof_start [partialRoundP128, partialRound, PartialRounds.circuit,
      PartialRounds.Spec]
    rcases h_env with ⟨hmid, hnext⟩
    have hnext0 := hnext ⟨0, by norm_num⟩
    have hnext1 := hnext ⟨1, by norm_num⟩
    have hnext2 := hnext ⟨2, by norm_num⟩
    norm_num at hnext0 hnext1 hnext2
    simp at hnext0 hnext1 hnext2
    rw [hmid, hnext0, hnext1, hnext2]
    change PartialRounds.Spec (partialParamsP128 roundConstants round)
      (partialRowValueP128 roundConstants round { x0 := input_x0, x1 := input_x1, x2 := input_x2 })
    simp [partialRowValueP128_spec]

/-- Apply the 28 consecutive P128Pow5T3 partial-round rows used by `Pow5Chip::permute`,
starting at source round 4.  Each row represents two source partial rounds. -/
def partialRoundRows28P128 (roundConstants : Nat → State Ecc.Fp)
    (state : Var State Ecc.Fp) : Circuit Ecc.Fp (Var State Ecc.Fp) :=
  Circuit.foldl (.finRange 28) state
    (fun state i => partialRoundP128Circuit roundConstants (4 + 2 * i.val) state)
    (by simp only [circuit_norm, partialRoundP128Circuit])
    (by
      apply Circuit.ConstantLength.fromConstantLength'
      simp [partialRoundP128Circuit, circuit_norm])

/-- Packaged fixed 28-row P128 partial-round loop. -/
def partialRoundRows28P128Circuit (roundConstants : Nat → State Ecc.Fp) :
    FormalCircuit Ecc.Fp State State where
  name := "Pow5State::partial_rounds[28][P128]"
  main := partialRoundRows28P128 roundConstants
  Spec input output := output = partialRoundRows28P128Value roundConstants input
  soundness := by
    circuit_proof_start [partialRoundRows28P128, partialRoundRows28P128Value,
      partialRoundP128Circuit]
    obtain ⟨h0, h_step⟩ := h_holds
    let inputState : State Ecc.Fp := { x0 := input_x0, x1 := input_x1, x2 := input_x2 }
    let envState : Nat → State Ecc.Fp := fun k =>
      if k = 0 then inputState else
        { x0 := env.get (i₀ + (k - 1) * (1 + [1, 1, 1].sum) + 1)
          x1 := env.get (i₀ + (k - 1) * (1 + [1, 1, 1].sum) + 1 + 1)
          x2 := env.get (i₀ + (k - 1) * (1 + [1, 1, 1].sum) + 1 + 1 + 1) }
    have hround : ∀ k (hk : k < 28),
        envState (k + 1) =
          partialRoundValue (partialParamsP128 roundConstants (4 + 2 * k)) (envState k) := by
      intro k hk
      cases k with
      | zero =>
          simp [envState, inputState]
          simpa using h0
      | succ j =>
          have hj := h_step j (by omega)
          simp [envState]
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.mul_add, Nat.add_mul] using hj
    have hind : ∀ k (hk : k ≤ 28),
        envState k = Fin.foldl k
          (fun state i => partialRoundValue (partialParamsP128 roundConstants (4 + 2 * i.val)) state)
          inputState := by
      intro k hk
      induction k with
      | zero => simp [envState, inputState]
      | succ k ih =>
          have hklt : k < 28 := by omega
          have ih' := ih (by omega)
          rw [Fin.foldl_succ_last]
          rw [show (fun x1 (x2 : Fin k) =>
              partialRoundValue (partialParamsP128 roundConstants (4 + 2 * ↑x2.castSucc)) x1) =
              (fun state (i : Fin k) =>
                partialRoundValue (partialParamsP128 roundConstants (4 + 2 * i.val)) state) from rfl]
          rw [← ih']
          simpa [show (Fin.last k).val = k by rfl] using hround k hklt
    have h28 := hind 28 (by omega)
    simpa [envState, inputState] using h28
  completeness := by
    circuit_proof_start [partialRoundRows28P128, partialRoundRows28P128Value,
      partialRoundP128Circuit]

/-- Apply the four consecutive full-round rows used by `Pow5Chip::permute`, starting
at source round `round`. -/
def fullRounds4 (roundConstants : Nat → State Ecc.Fp) (mds : Nat → Nat → Ecc.Fp)
    (round : Nat) (state : Var State Ecc.Fp) : Circuit Ecc.Fp (Var State Ecc.Fp) :=
  Circuit.foldl (.finRange 4) state
    (fun state i => fullRoundCircuit (fullParams roundConstants mds (round + i.val)) state)
    (by simp only [circuit_norm, fullRoundCircuit])
    (by
      apply Circuit.ConstantLength.fromConstantLength'
      simp [fullRoundCircuit, circuit_norm])

/-- Packaged four-full-round loop used by each half of `Pow5Chip::permute`. -/
def fullRounds4Circuit (roundConstants : Nat → State Ecc.Fp) (mds : Nat → Nat → Ecc.Fp)
    (round : Nat) : FormalCircuit Ecc.Fp State State where
  name := "Pow5State::full_rounds[4]"
  main := fullRounds4 roundConstants mds round
  Spec input output := output = fullRounds4Value roundConstants mds round input
  soundness := by
    circuit_proof_start [fullRounds4, fullRounds4Value, fullRoundCircuit]
    obtain ⟨h0, h_step⟩ := h_holds
    have h1 := h_step 0 (by norm_num)
    have h2 := h_step 1 (by norm_num)
    have h3 := h_step 2 (by norm_num)
    simp only [Fin.foldl_succ_last, Fin.foldl_zero] at h0 h1 h2 h3 ⊢
    norm_num at h1 h2 h3 ⊢
    rw [h0] at h1
    rw [h1] at h2
    rw [h2] at h3
    simpa using h3
  completeness := by
    circuit_proof_start [fullRounds4, fullRounds4Value, fullRoundCircuit]

/-- Apply the 28 consecutive partial-round rows used by `Pow5Chip::permute`, starting
at source round 4.  Each row represents two source partial rounds. -/
def partialRoundRows28 (roundConstants : Nat → State Ecc.Fp) (mds mdsInv : Nat → Nat → Ecc.Fp)
    (state : Var State Ecc.Fp) : Circuit Ecc.Fp (Var State Ecc.Fp) :=
  Circuit.foldl (.finRange 28) state
    (fun state i => partialRound (partialParams roundConstants mds mdsInv (4 + 2 * i.val)) state)
    (by simp only [circuit_norm, partialRound])
    (by
      apply Circuit.ConstantLength.fromConstantLength'
      simp [partialRound, PartialRounds.circuit, circuit_norm])

/-- `Pow5Chip::permute` for Orchard's width-3/rate-2 Poseidon instance. -/
def main (roundConstants : Nat → State Ecc.Fp) (mds mdsInv : Nat → Nat → Ecc.Fp)
    (input : Var State Ecc.Fp) : Circuit Ecc.Fp (Var State Ecc.Fp) := do
  let s ← fullRounds4Circuit roundConstants mds 0 input
  let s ← partialRoundRows28 roundConstants mds mdsInv s
  fullRounds4Circuit roundConstants mds (4 + 56) s

/-- P128Pow5T3-specialized `Pow5Chip::permute` circuit shape. -/
def mainP128 (roundConstants : Nat → State Ecc.Fp)
    (input : Var State Ecc.Fp) : Circuit Ecc.Fp (Var State Ecc.Fp) := do
  let s ← fullRounds4Circuit roundConstants P128Pow5T3.mds 0 input
  let s ← partialRoundRows28P128Circuit roundConstants s
  fullRounds4Circuit roundConstants P128Pow5T3.mds (4 + 56) s

/-- Packaged P128Pow5T3 `Pow5Chip::permute` circuit. -/
def mainP128Circuit (roundConstants : Nat → State Ecc.Fp) :
    FormalCircuit Ecc.Fp State State where
  name := "Pow5Chip::permute[P128]"
  main := mainP128 roundConstants
  Spec input output := output = permuteP128Value roundConstants input
  soundness := by
    circuit_proof_start [mainP128, permuteP128Value, fullRounds4Circuit,
      partialRoundRows28P128Circuit]
    rcases h_holds with ⟨hfull0, hpartial, hfull1⟩
    rw [hfull0] at hpartial
    rw [hpartial] at hfull1
    simpa using hfull1
  completeness := by
    circuit_proof_start [mainP128, permuteP128Value, fullRounds4Circuit,
      partialRoundRows28P128Circuit]

/-!
The P128-specialized permutation is packaged as `mainP128Circuit`.  The parameterized
compatibility wrapper `main` remains available for experiments with non-P128 constants,
but it is intentionally not packaged because the partial-row proof relies on the explicit
P128 MDS inverse lemmas.
-/

end Permute

end Poseidon
end Orchard
