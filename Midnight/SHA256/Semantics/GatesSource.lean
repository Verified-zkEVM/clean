import Midnight.SHA256.Configure
import Midnight.SHA256.Synthesis
import Clean.Halo2.Lemmas

/-! Semantic extraction from the source-configured SHA gates. The small literal
ASTs below are kernel-checked against `cleanGates` by selector. Keeping those
checked shapes separate avoids reducing the entire configuration in row proofs. -/

namespace Midnight.SHA256.Semantics.Gates
open Halo2 Midnight.Keygen

def majSpec : GateSpec :=
  let sA : E := .var (.advice ⟨3⟩ (-1))
  let sB : E := .var (.advice ⟨4⟩ (-1))
  let sC : E := .var (.advice ⟨3⟩ (0))
  let s_odd_11a : E := .var (.advice ⟨0⟩ (-1))
  let s_odd_11b : E := .var (.advice ⟨0⟩ (0))
  let s_odd_010 : E := .var (.advice ⟨0⟩ (1))
  let s_evn_11a : E := .var (.advice ⟨1⟩ (-1))
  let s_evn_11b : E := .var (.advice ⟨1⟩ (0))
  let s_evn_010 : E := .var (.advice ⟨1⟩ (1))
  let s_evn := pow4ip [21, 10, 0] [s_evn_11a, s_evn_11b, s_evn_010]
  let s_odd := pow4ip [21, 10, 0] [s_odd_11a, s_odd_11b, s_odd_010]
  let id := (sA + sB + sC) - (s_evn + (.const 2 : E) * s_odd)
  { name := "Maj(A, B, C)", selector := ⟨5, true⟩,
    queries := #[.advice ⟨3⟩ (-1), .advice ⟨4⟩ (-1), .advice ⟨3⟩ (0), .advice ⟨0⟩ (-1), .advice ⟨0⟩ (0), .advice ⟨0⟩ (1), .advice ⟨1⟩ (-1), .advice ⟨1⟩ (0), .advice ⟨1⟩ (1)],
    constraints := #[("Maj", id)] }

def majGate : Gate F := majSpec.toClean (by decide +kernel)

theorem majGate_source :
    cleanGates.filter (fun g => g.selector.index == 5) = [majGate] := by
  decide +kernel

theorem activation_maj (row : Nat) : activation 5 row = [.enableGate majGate row] := by
  have hl : cleanLookups.filter (fun l => l.masterSelector.index == 5) = [] := by decide +kernel
  simp [activation, majGate_source, hl]

def halfChSpec : GateSpec :=
  let sX : E := .var (.advice ⟨3⟩ (-1))
  let sY : E := .var (.advice ⟨4⟩ (-1))
  let s_odd_11a : E := .var (.advice ⟨0⟩ (-1))
  let s_odd_11b : E := .var (.advice ⟨0⟩ (0))
  let s_odd_010 : E := .var (.advice ⟨0⟩ (1))
  let s_evn_11a : E := .var (.advice ⟨1⟩ (-1))
  let s_evn_11b : E := .var (.advice ⟨1⟩ (0))
  let s_evn_010 : E := .var (.advice ⟨1⟩ (1))
  let summand_1 : E := .var (.advice ⟨2⟩ (0))
  let summand_2 : E := .var (.advice ⟨3⟩ (0))
  let sum : E := .var (.advice ⟨4⟩ (0))
  let s_evn := pow4ip [21, 10, 0] [s_evn_11a, s_evn_11b, s_evn_010]
  let s_odd := pow4ip [21, 10, 0] [s_odd_11a, s_odd_11b, s_odd_010]
  let sprdd_id := (sX + sY) - (s_evn + (.const 2 : E) * s_odd)
  let sum_id := (summand_1 + summand_2) - sum
  { name := "half Ch(E, F, G)", selector := ⟨6, true⟩,
    queries := #[.advice ⟨3⟩ (-1), .advice ⟨4⟩ (-1), .advice ⟨0⟩ (-1), .advice ⟨0⟩ (0), .advice ⟨0⟩ (1), .advice ⟨1⟩ (-1), .advice ⟨1⟩ (0), .advice ⟨1⟩ (1), .advice ⟨2⟩ (0), .advice ⟨3⟩ (0), .advice ⟨4⟩ (0)],
    constraints := #[("Half-Ch spreadded", sprdd_id), ("Half Ch sum (2 terms)", sum_id)] }

def halfChGate : Gate F := halfChSpec.toClean (by decide +kernel)

theorem halfChGate_source :
    cleanGates.filter (fun g => g.selector.index == 6) = [halfChGate] := by
  decide +kernel

theorem activation_halfCh (row : Nat) : activation 6 row = [.enableGate halfChGate row] := by
  have hl : cleanLookups.filter (fun l => l.masterSelector.index == 6) = [] := by decide +kernel
  simp [activation, halfChGate_source, hl]

def bigSigma0Spec : GateSpec :=
  let s10 : E := .var (.advice ⟨3⟩ (-1))
  let s09 : E := .var (.advice ⟨4⟩ (-1))
  let s11 : E := .var (.advice ⟨3⟩ (0))
  let s02 : E := .var (.advice ⟨4⟩ (0))
  let s_evn_11a : E := .var (.advice ⟨0⟩ (-1))
  let s_evn_11b : E := .var (.advice ⟨0⟩ (0))
  let s_evn_010 : E := .var (.advice ⟨0⟩ (1))
  let s_odd_11a : E := .var (.advice ⟨1⟩ (-1))
  let s_odd_11b : E := .var (.advice ⟨1⟩ (0))
  let s_odd_010 : E := .var (.advice ⟨1⟩ (1))
  let s_1st_rot := pow4ip [30, 20, 11, 0] [s02, s10, s09, s11]
  let s_2nd_rot := pow4ip [21, 19, 9, 0] [s11, s02, s10, s09]
  let s_3rd_rot := pow4ip [23, 12, 10, 0] [s09, s11, s02, s10]
  let s_evn := pow4ip [21, 10, 0] [s_evn_11a, s_evn_11b, s_evn_010]
  let s_odd := pow4ip [21, 10, 0] [s_odd_11a, s_odd_11b, s_odd_010]
  let id := (s_1st_rot + s_2nd_rot + s_3rd_rot) - (s_evn + (.const 2 : E) * s_odd)
  { name := "Σ₀(A)", selector := ⟨7, true⟩,
    queries := #[.advice ⟨3⟩ (-1), .advice ⟨4⟩ (-1), .advice ⟨3⟩ (0), .advice ⟨4⟩ (0), .advice ⟨0⟩ (-1), .advice ⟨0⟩ (0), .advice ⟨0⟩ (1), .advice ⟨1⟩ (-1), .advice ⟨1⟩ (0), .advice ⟨1⟩ (1)],
    constraints := #[("Sigma_0", id)] }

def bigSigma0Gate : Gate F := bigSigma0Spec.toClean (by decide +kernel)

theorem bigSigma0Gate_source :
    cleanGates.filter (fun g => g.selector.index == 7) = [bigSigma0Gate] := by
  decide +kernel

theorem activation_bigSigma0 (row : Nat) : activation 7 row = [.enableGate bigSigma0Gate row] := by
  have hl : cleanLookups.filter (fun l => l.masterSelector.index == 7) = [] := by decide +kernel
  simp [activation, bigSigma0Gate_source, hl]

def bigSigma1Spec : GateSpec :=
  let s07 : E := .var (.advice ⟨3⟩ (-1))
  let s12 : E := .var (.advice ⟨4⟩ (-1))
  let s02 : E := .var (.advice ⟨3⟩ (0))
  let s05 : E := .var (.advice ⟨4⟩ (0))
  let s06 : E := .var (.advice ⟨3⟩ (1))
  let s_evn_11a : E := .var (.advice ⟨0⟩ (-1))
  let s_evn_11b : E := .var (.advice ⟨0⟩ (0))
  let s_evn_10 : E := .var (.advice ⟨0⟩ (1))
  let s_odd_11a : E := .var (.advice ⟨1⟩ (-1))
  let s_odd_11b : E := .var (.advice ⟨1⟩ (0))
  let s_odd_10 : E := .var (.advice ⟨1⟩ (1))
  let s_1st_rot := pow4ip [26, 19, 7, 5, 0] [s06, s07, s12, s02, s05]
  let s_2nd_rot := pow4ip [27, 21, 14, 2, 0] [s05, s06, s07, s12, s02]
  let s_3rd_rot := pow4ip [20, 18, 13, 7, 0] [s12, s02, s05, s06, s07]
  let s_evn := pow4ip [21, 10, 0] [s_evn_11a, s_evn_11b, s_evn_10]
  let s_odd := pow4ip [21, 10, 0] [s_odd_11a, s_odd_11b, s_odd_10]
  let id := (s_1st_rot + s_2nd_rot + s_3rd_rot) - (s_evn + (.const 2 : E) * s_odd)
  { name := "Σ₁(E)", selector := ⟨8, true⟩,
    queries := #[.advice ⟨3⟩ (-1), .advice ⟨4⟩ (-1), .advice ⟨3⟩ (0), .advice ⟨4⟩ (0), .advice ⟨3⟩ (1), .advice ⟨0⟩ (-1), .advice ⟨0⟩ (0), .advice ⟨0⟩ (1), .advice ⟨1⟩ (-1), .advice ⟨1⟩ (0), .advice ⟨1⟩ (1)],
    constraints := #[("Sigma_1", id)] }

def bigSigma1Gate : Gate F := bigSigma1Spec.toClean (by decide +kernel)

theorem bigSigma1Gate_source :
    cleanGates.filter (fun g => g.selector.index == 8) = [bigSigma1Gate] := by
  decide +kernel

theorem activation_bigSigma1 (row : Nat) : activation 8 row = [.enableGate bigSigma1Gate row] := by
  have hl : cleanLookups.filter (fun l => l.masterSelector.index == 8) = [] := by decide +kernel
  simp [activation, bigSigma1Gate_source, hl]

def sigma0Spec : GateSpec :=
  let s12 : E := .var (.advice ⟨3⟩ (-1))
  let s1a : E := .var (.advice ⟨4⟩ (-1))
  let s1b : E := .var (.advice ⟨2⟩ (0))
  let s1c : E := .var (.advice ⟨3⟩ (0))
  let s07 : E := .var (.advice ⟨4⟩ (0))
  let s3a : E := .var (.advice ⟨2⟩ (1))
  let s04 : E := .var (.advice ⟨3⟩ (1))
  let s3b : E := .var (.advice ⟨4⟩ (1))
  let s_evn_11a : E := .var (.advice ⟨0⟩ (-1))
  let s_evn_11b : E := .var (.advice ⟨0⟩ (0))
  let s_evn_10 : E := .var (.advice ⟨0⟩ (1))
  let s_odd_11a : E := .var (.advice ⟨1⟩ (-1))
  let s_odd_11b : E := .var (.advice ⟨1⟩ (0))
  let s_odd_10 : E := .var (.advice ⟨1⟩ (1))
  let sprdd_1st_shift := pow4ip [17, 16, 15, 14, 7, 4, 0] [s12, s1a, s1b, s1c, s07, s3a, s04]
  let sprdd_2nd_rot := pow4ip [28, 25, 13, 12, 11, 10, 3, 0] [s04, s3b, s12, s1a, s1b, s1c, s07, s3a]
  let sprdd_3rd_rot := pow4ip [31, 24, 21, 17, 14, 2, 1, 0] [s1c, s07, s3a, s04, s3b, s12, s1a, s1b]
  let sprdd_evn := pow4ip [21, 10, 0] [s_evn_11a, s_evn_11b, s_evn_10]
  let sprdd_odd := pow4ip [21, 10, 0] [s_odd_11a, s_odd_11b, s_odd_10]
  let id := (sprdd_1st_shift + sprdd_2nd_rot + sprdd_3rd_rot) - (sprdd_evn + (.const 2 : E) * sprdd_odd)
  { name := "σ₀(W)", selector := ⟨9, true⟩,
    queries := #[.advice ⟨3⟩ (-1), .advice ⟨4⟩ (-1), .advice ⟨2⟩ (0), .advice ⟨3⟩ (0), .advice ⟨4⟩ (0), .advice ⟨2⟩ (1), .advice ⟨3⟩ (1), .advice ⟨4⟩ (1), .advice ⟨0⟩ (-1), .advice ⟨0⟩ (0), .advice ⟨0⟩ (1), .advice ⟨1⟩ (-1), .advice ⟨1⟩ (0), .advice ⟨1⟩ (1)],
    constraints := #[("sigma_0", id)] }

def sigma0Gate : Gate F := sigma0Spec.toClean (by decide +kernel)

theorem sigma0Gate_source :
    cleanGates.filter (fun g => g.selector.index == 9) = [sigma0Gate] := by
  decide +kernel

theorem activation_sigma0 (row : Nat) : activation 9 row = [.enableGate sigma0Gate row] := by
  have hl : cleanLookups.filter (fun l => l.masterSelector.index == 9) = [] := by decide +kernel
  simp [activation, sigma0Gate_source, hl]

def sigma1Spec : GateSpec :=
  let s12 : E := .var (.advice ⟨3⟩ (-1))
  let s1a : E := .var (.advice ⟨4⟩ (-1))
  let s1b : E := .var (.advice ⟨2⟩ (0))
  let s1c : E := .var (.advice ⟨3⟩ (0))
  let s07 : E := .var (.advice ⟨4⟩ (0))
  let s3a : E := .var (.advice ⟨2⟩ (1))
  let s04 : E := .var (.advice ⟨3⟩ (1))
  let s3b : E := .var (.advice ⟨4⟩ (1))
  let s_evn_11a : E := .var (.advice ⟨0⟩ (-1))
  let s_evn_11b : E := .var (.advice ⟨0⟩ (0))
  let s_evn_10 : E := .var (.advice ⟨0⟩ (1))
  let s_odd_11a : E := .var (.advice ⟨1⟩ (-1))
  let s_odd_11b : E := .var (.advice ⟨1⟩ (0))
  let s_odd_10 : E := .var (.advice ⟨1⟩ (1))
  let sprdd_1st_shift := pow4ip [10, 9, 8, 7, 0] [s12, s1a, s1b, s1c, s07]
  let sprdd_2nd_rot := pow4ip [25, 22, 18, 15, 3, 2, 1, 0] [s07, s3a, s04, s3b, s12, s1a, s1b, s1c]
  let sprdd_3rd_rot := pow4ip [31, 30, 23, 20, 16, 13, 1, 0] [s1b, s1c, s07, s3a, s04, s3b, s12, s1a]
  let sprdd_evn := pow4ip [21, 10, 0] [s_evn_11a, s_evn_11b, s_evn_10]
  let sprdd_odd := pow4ip [21, 10, 0] [s_odd_11a, s_odd_11b, s_odd_10]
  let id := (sprdd_1st_shift + sprdd_2nd_rot + sprdd_3rd_rot) - (sprdd_evn + (.const 2 : E) * sprdd_odd)
  { name := "σ₁(W)", selector := ⟨10, true⟩,
    queries := #[.advice ⟨3⟩ (-1), .advice ⟨4⟩ (-1), .advice ⟨2⟩ (0), .advice ⟨3⟩ (0), .advice ⟨4⟩ (0), .advice ⟨2⟩ (1), .advice ⟨3⟩ (1), .advice ⟨4⟩ (1), .advice ⟨0⟩ (-1), .advice ⟨0⟩ (0), .advice ⟨0⟩ (1), .advice ⟨1⟩ (-1), .advice ⟨1⟩ (0), .advice ⟨1⟩ (1)],
    constraints := #[("sigma_1", id)] }

def sigma1Gate : Gate F := sigma1Spec.toClean (by decide +kernel)

theorem sigma1Gate_source :
    cleanGates.filter (fun g => g.selector.index == 10) = [sigma1Gate] := by
  decide +kernel

theorem activation_sigma1 (row : Nat) : activation 10 row = [.enableGate sigma1Gate row] := by
  have hl : cleanLookups.filter (fun l => l.masterSelector.index == 10) = [] := by decide +kernel
  simp [activation, sigma1Gate_source, hl]

def paritySpec : GateSpec :=
  let p11a : E := .var (.advice ⟨6⟩ (-1))
  let p11b : E := .var (.advice ⟨6⟩ (0))
  let p_10 : E := .var (.advice ⟨6⟩ (1))
  let output : E := .var (.advice ⟨2⟩ (-1))
  let id := pow2ip [21, 10, 0] [p11a, p11b, p_10] - output
  { name := "11-11-10 decomposition", selector := ⟨11, true⟩,
    queries := #[.advice ⟨6⟩ (-1), .advice ⟨6⟩ (0), .advice ⟨6⟩ (1), .advice ⟨2⟩ (-1)],
    constraints := #[("11-11-10 decomposition", id)] }

def parityGate : Gate F := paritySpec.toClean (by decide +kernel)

theorem parityGate_source :
    cleanGates.filter (fun g => g.selector.index == 11) = [parityGate] := by
  decide +kernel

theorem activation_parity (row : Nat) : activation 11 row = [.enableGate parityGate row] := by
  have hl : cleanLookups.filter (fun l => l.masterSelector.index == 11) = [] := by decide +kernel
  simp [activation, parityGate_source, hl]

def aSpec : GateSpec :=
  let p10 : E := .var (.advice ⟨6⟩ (-1))
  let p09 : E := .var (.advice ⟨7⟩ (-1))
  let p11 : E := .var (.advice ⟨6⟩ (0))
  let p02 : E := .var (.advice ⟨7⟩ (0))
  let s10 : E := .var (.advice ⟨0⟩ (-1))
  let s09 : E := .var (.advice ⟨1⟩ (-1))
  let s11 : E := .var (.advice ⟨0⟩ (0))
  let s02 : E := .var (.advice ⟨1⟩ (0))
  let plain : E := .var (.advice ⟨2⟩ (-1))
  let sprdd : E := .var (.advice ⟨2⟩ (0))
  let plain_id := pow2ip [22, 13, 2, 0] [p10, p09, p11, p02] - plain
  let sprdd_id := pow4ip [22, 13, 2, 0] [s10, s09, s11, s02] - sprdd
  { name := "10-9-11-2 decomposition", selector := ⟨12, true⟩,
    queries := #[.advice ⟨6⟩ (-1), .advice ⟨7⟩ (-1), .advice ⟨6⟩ (0), .advice ⟨7⟩ (0), .advice ⟨0⟩ (-1), .advice ⟨1⟩ (-1), .advice ⟨0⟩ (0), .advice ⟨1⟩ (0), .advice ⟨2⟩ (-1), .advice ⟨2⟩ (0)],
    constraints := #[("10_9_11_2 decomposition plain", plain_id), ("10_9_11_2 decomposition sprdd", sprdd_id)] }

def aGate : Gate F := aSpec.toClean (by decide +kernel)

theorem aGate_source :
    cleanGates.filter (fun g => g.selector.index == 12) = [aGate] := by
  decide +kernel

theorem activation_a (row : Nat) : activation 12 row = [.enableGate aGate row] := by
  have hl : cleanLookups.filter (fun l => l.masterSelector.index == 12) = [] := by decide +kernel
  simp [activation, aGate_source, hl]

def eSpec : GateSpec :=
  let p07 : E := .var (.advice ⟨6⟩ (-1))
  let p12 : E := .var (.advice ⟨7⟩ (-1))
  let p02 : E := .var (.advice ⟨6⟩ (0))
  let p05 : E := .var (.advice ⟨7⟩ (0))
  let p06 : E := .var (.advice ⟨6⟩ (1))
  let s07 : E := .var (.advice ⟨0⟩ (-1))
  let s12 : E := .var (.advice ⟨1⟩ (-1))
  let s02 : E := .var (.advice ⟨0⟩ (0))
  let s05 : E := .var (.advice ⟨1⟩ (0))
  let s06 : E := .var (.advice ⟨0⟩ (1))
  let plain : E := .var (.advice ⟨2⟩ (-1))
  let sprdd : E := .var (.advice ⟨2⟩ (0))
  let plain_id := pow2ip [25, 13, 11, 6, 0] [p07, p12, p02, p05, p06] - plain
  let sprdd_id := pow4ip [25, 13, 11, 6, 0] [s07, s12, s02, s05, s06] - sprdd
  { name := "7-12-2-5-6 decomposition", selector := ⟨13, true⟩,
    queries := #[.advice ⟨6⟩ (-1), .advice ⟨7⟩ (-1), .advice ⟨6⟩ (0), .advice ⟨7⟩ (0), .advice ⟨6⟩ (1), .advice ⟨0⟩ (-1), .advice ⟨1⟩ (-1), .advice ⟨0⟩ (0), .advice ⟨1⟩ (0), .advice ⟨0⟩ (1), .advice ⟨2⟩ (-1), .advice ⟨2⟩ (0)],
    constraints := #[("7_12_2_5_6 decomposition plain", plain_id), ("7_12_2_5_6 decomposition sprdd", sprdd_id)] }

def eGate : Gate F := eSpec.toClean (by decide +kernel)

theorem eGate_source :
    cleanGates.filter (fun g => g.selector.index == 13) = [eGate] := by
  decide +kernel

theorem activation_e (row : Nat) : activation 13 row = [.enableGate eGate row] := by
  have hl : cleanLookups.filter (fun l => l.masterSelector.index == 13) = [] := by decide +kernel
  simp [activation, eGate_source, hl]

def messageSpec : GateSpec :=
  let w12 : E := .var (.advice ⟨6⟩ (-1))
  let w07 : E := .var (.advice ⟨7⟩ (-1))
  let w3a : E := .var (.advice ⟨6⟩ (0))
  let w04 : E := .var (.advice ⟨7⟩ (0))
  let w3b : E := .var (.advice ⟨6⟩ (1))
  let w1a : E := .var (.advice ⟨5⟩ (-1))
  let w1b : E := .var (.advice ⟨5⟩ (0))
  let w1c : E := .var (.advice ⟨5⟩ (1))
  let plain : E := .var (.advice ⟨2⟩ (-1))
  let plain_id := pow2ip [20, 19, 18, 17, 10, 7, 3, 0] [w12, w1a, w1b, w1c, w07, w3a, w04, w3b] - plain
  let w_1a_check := w1a * (w1a - (.const 1 : E))
  let w_1b_check := w1b * (w1b - (.const 1 : E))
  let w_1c_check := w1c * (w1c - (.const 1 : E))
  { name := "12-1x3-7-3-4-3 decomposition", selector := ⟨14, true⟩,
    queries := #[.advice ⟨6⟩ (-1), .advice ⟨7⟩ (-1), .advice ⟨6⟩ (0), .advice ⟨7⟩ (0), .advice ⟨6⟩ (1), .advice ⟨5⟩ (-1), .advice ⟨5⟩ (0), .advice ⟨5⟩ (1), .advice ⟨2⟩ (-1)],
    constraints := #[("12_1x3_7_3_4_3 decomposition ", plain_id), ("W.1a 1-bit check", w_1a_check), ("W.1b 1-bit check", w_1b_check), ("W.1c 1-bit check", w_1c_check)] }

def messageGate : Gate F := messageSpec.toClean (by decide +kernel)

theorem messageGate_source :
    cleanGates.filter (fun g => g.selector.index == 14) = [messageGate] := by
  decide +kernel

theorem activation_message (row : Nat) : activation 14 row = [.enableGate messageGate row] := by
  have hl : cleanLookups.filter (fun l => l.masterSelector.index == 14) = [] := by decide +kernel
  simp [activation, messageGate_source, hl]

def addModSpec : GateSpec :=
  let s0 : E := .var (.advice ⟨3⟩ (-1))
  let s1 : E := .var (.advice ⟨4⟩ (-1))
  let s2 : E := .var (.advice ⟨3⟩ (0))
  let s3 : E := .var (.advice ⟨4⟩ (0))
  let s4 : E := .var (.advice ⟨2⟩ (1))
  let s5 : E := .var (.advice ⟨3⟩ (1))
  let s6 : E := .var (.advice ⟨4⟩ (1))
  let carry : E := .var (.advice ⟨7⟩ (1))
  let result : E := .var (.advice ⟨2⟩ (-1))
  let summands := [s0, s1, s2, s3, s4, s5, s6]
  let lhs := sumExpr summands
  let rhs := result + carry.mulConstant (2 ^ 32)
  { name := "add mod 2^32", selector := ⟨15, true⟩,
    queries := #[.advice ⟨3⟩ (-1), .advice ⟨4⟩ (-1), .advice ⟨3⟩ (0), .advice ⟨4⟩ (0), .advice ⟨2⟩ (1), .advice ⟨3⟩ (1), .advice ⟨4⟩ (1), .advice ⟨7⟩ (1), .advice ⟨2⟩ (-1)],
    constraints := #[("add_mod_2_32", lhs - rhs)] }

def addModGate : Gate F := addModSpec.toClean (by decide +kernel)

theorem addModGate_source :
    cleanGates.filter (fun g => g.selector.index == 15) = [addModGate] := by
  decide +kernel

theorem activation_addMod (row : Nat) : activation 15 row = [.enableGate addModGate row] := by
  have hl : cleanLookups.filter (fun l => l.masterSelector.index == 15) = [] := by decide +kernel
  simp [activation, addModGate_source, hl]

/-- Read a logical SHA advice column through the source architecture mapping. -/
def read (env : Environment F) (absolute : Int) (column : Fin 8) (rotation : Int) : F :=
  env.advice ⟨Synthesis.shaAdvice[column.val]'(by simp [Synthesis.shaAdvice])⟩
    (absolute + rotation)

/-- Reconstruct one 11/11/10 spread bit-plane from its actual three query rows. -/
def parityPlane (env : Environment F) (absolute : Int) (column : Fin 8) : F :=
  (2 ^ 42 : F) * read env absolute column (-1) +
    (2 ^ 20 : F) * read env absolute column 0 + read env absolute column 1

end Midnight.SHA256.Semantics.Gates
