/-
BN254 Poseidon constants for the circomlib instances with state widths 2-17.

The values are generated deterministically during elaboration, then emitted as
ordinary typed vectors. This keeps the public C_t*/M_t*/P_t*/S_t* interface
and downstream compilation behavior without checking a 1.69 MB literal table
into the repository.

Before the literal table was removed, Lean checked all 24,060 generated values
for exact equality with it, and an independent Python implementation checked
the same values against the original constants from:

  iden3/circomlib commit 35e54ea21da3e8762557234298dbb553c175ea8d
  circuits/poseidon_constants.circom
  SHA-256 94c9e4b5ea891ab4d1ba626f1d719f8c661014d9b628f6096c803f75f39e3eee

The compact independent audit in scripts/reproduce_poseidon_constants.py pins
digests of those checked values and can also compare directly with that source.
Normal builds are deterministic and offline; no external checkout is required.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Clean.Specs.PoseidonParameterElaboration

@[expose] public section

namespace Specs.Poseidon.ParameterGeneration.Generated

set_option maxRecDepth 8192 in
def t2 : GeneratedVectors 2 56 := poseidon_parameters% 2 56

set_option maxRecDepth 8192 in
def t3 : GeneratedVectors 3 57 := poseidon_parameters% 3 57

set_option maxRecDepth 8192 in
def t4 : GeneratedVectors 4 56 := poseidon_parameters% 4 56

set_option maxRecDepth 8192 in
def t5 : GeneratedVectors 5 60 := poseidon_parameters% 5 60

set_option maxRecDepth 8192 in
def t6 : GeneratedVectors 6 60 := poseidon_parameters% 6 60

set_option maxRecDepth 8192 in
def t7 : GeneratedVectors 7 63 := poseidon_parameters% 7 63

set_option maxRecDepth 8192 in
def t8 : GeneratedVectors 8 64 := poseidon_parameters% 8 64

set_option maxRecDepth 8192 in
def t9 : GeneratedVectors 9 63 := poseidon_parameters% 9 63

set_option maxRecDepth 8192 in
def t10 : GeneratedVectors 10 60 := poseidon_parameters% 10 60

set_option maxRecDepth 8192 in
def t11 : GeneratedVectors 11 66 := poseidon_parameters% 11 66

set_option maxRecDepth 8192 in
def t12 : GeneratedVectors 12 60 := poseidon_parameters% 12 60

set_option maxRecDepth 32768 in
def t13 : GeneratedVectors 13 65 := poseidon_parameters% 13 65

set_option maxRecDepth 32768 in
def t14 : GeneratedVectors 14 70 := poseidon_parameters% 14 70

set_option maxRecDepth 32768 in
def t15 : GeneratedVectors 15 60 := poseidon_parameters% 15 60

set_option maxRecDepth 32768 in
def t16 : GeneratedVectors 16 64 := poseidon_parameters% 16 64

set_option maxRecDepth 32768 in
def t17 : GeneratedVectors 17 68 := poseidon_parameters% 17 68

end Specs.Poseidon.ParameterGeneration.Generated

namespace Specs.Poseidon

def C_t2 : Vector ℕ 72 := ParameterGeneration.Generated.t2.C
def M_t2 : Vector (Vector ℕ 2) 2 := ParameterGeneration.Generated.t2.M

def C_t3 : Vector ℕ 81 := ParameterGeneration.Generated.t3.C
def M_t3 : Vector (Vector ℕ 3) 3 := ParameterGeneration.Generated.t3.M

def C_t4 : Vector ℕ 88 := ParameterGeneration.Generated.t4.C
def M_t4 : Vector (Vector ℕ 4) 4 := ParameterGeneration.Generated.t4.M

def C_t5 : Vector ℕ 100 := ParameterGeneration.Generated.t5.C
def M_t5 : Vector (Vector ℕ 5) 5 := ParameterGeneration.Generated.t5.M

def C_t6 : Vector ℕ 108 := ParameterGeneration.Generated.t6.C
def M_t6 : Vector (Vector ℕ 6) 6 := ParameterGeneration.Generated.t6.M

def C_t7 : Vector ℕ 119 := ParameterGeneration.Generated.t7.C
def M_t7 : Vector (Vector ℕ 7) 7 := ParameterGeneration.Generated.t7.M

def C_t8 : Vector ℕ 128 := ParameterGeneration.Generated.t8.C
def M_t8 : Vector (Vector ℕ 8) 8 := ParameterGeneration.Generated.t8.M

def C_t9 : Vector ℕ 135 := ParameterGeneration.Generated.t9.C
def M_t9 : Vector (Vector ℕ 9) 9 := ParameterGeneration.Generated.t9.M

def C_t10 : Vector ℕ 140 := ParameterGeneration.Generated.t10.C
def M_t10 : Vector (Vector ℕ 10) 10 := ParameterGeneration.Generated.t10.M

def C_t11 : Vector ℕ 154 := ParameterGeneration.Generated.t11.C
def M_t11 : Vector (Vector ℕ 11) 11 := ParameterGeneration.Generated.t11.M

def C_t12 : Vector ℕ 156 := ParameterGeneration.Generated.t12.C
def M_t12 : Vector (Vector ℕ 12) 12 := ParameterGeneration.Generated.t12.M

def C_t13 : Vector ℕ 169 := ParameterGeneration.Generated.t13.C
def M_t13 : Vector (Vector ℕ 13) 13 := ParameterGeneration.Generated.t13.M

def C_t14 : Vector ℕ 182 := ParameterGeneration.Generated.t14.C
def M_t14 : Vector (Vector ℕ 14) 14 := ParameterGeneration.Generated.t14.M

def C_t15 : Vector ℕ 180 := ParameterGeneration.Generated.t15.C
def M_t15 : Vector (Vector ℕ 15) 15 := ParameterGeneration.Generated.t15.M

def C_t16 : Vector ℕ 192 := ParameterGeneration.Generated.t16.C
def M_t16 : Vector (Vector ℕ 16) 16 := ParameterGeneration.Generated.t16.M

def C_t17 : Vector ℕ 204 := ParameterGeneration.Generated.t17.C
def M_t17 : Vector (Vector ℕ 17) 17 := ParameterGeneration.Generated.t17.M

end Specs.Poseidon

namespace Specs.PoseidonOptimized

def P_t2 : Vector (Vector ℕ 2) 2 :=
  Specs.Poseidon.ParameterGeneration.Generated.t2.P
def S_t2 : Vector ℕ 168 :=
  Specs.Poseidon.ParameterGeneration.Generated.t2.S

def P_t3 : Vector (Vector ℕ 3) 3 :=
  Specs.Poseidon.ParameterGeneration.Generated.t3.P
def S_t3 : Vector ℕ 285 :=
  Specs.Poseidon.ParameterGeneration.Generated.t3.S

def P_t4 : Vector (Vector ℕ 4) 4 :=
  Specs.Poseidon.ParameterGeneration.Generated.t4.P
def S_t4 : Vector ℕ 392 :=
  Specs.Poseidon.ParameterGeneration.Generated.t4.S

def P_t5 : Vector (Vector ℕ 5) 5 :=
  Specs.Poseidon.ParameterGeneration.Generated.t5.P
def S_t5 : Vector ℕ 540 :=
  Specs.Poseidon.ParameterGeneration.Generated.t5.S

def P_t6 : Vector (Vector ℕ 6) 6 :=
  Specs.Poseidon.ParameterGeneration.Generated.t6.P
def S_t6 : Vector ℕ 660 :=
  Specs.Poseidon.ParameterGeneration.Generated.t6.S

def P_t7 : Vector (Vector ℕ 7) 7 :=
  Specs.Poseidon.ParameterGeneration.Generated.t7.P
def S_t7 : Vector ℕ 819 :=
  Specs.Poseidon.ParameterGeneration.Generated.t7.S

def P_t8 : Vector (Vector ℕ 8) 8 :=
  Specs.Poseidon.ParameterGeneration.Generated.t8.P
def S_t8 : Vector ℕ 960 :=
  Specs.Poseidon.ParameterGeneration.Generated.t8.S

def P_t9 : Vector (Vector ℕ 9) 9 :=
  Specs.Poseidon.ParameterGeneration.Generated.t9.P
def S_t9 : Vector ℕ 1071 :=
  Specs.Poseidon.ParameterGeneration.Generated.t9.S

def P_t10 : Vector (Vector ℕ 10) 10 :=
  Specs.Poseidon.ParameterGeneration.Generated.t10.P
def S_t10 : Vector ℕ 1140 :=
  Specs.Poseidon.ParameterGeneration.Generated.t10.S

def P_t11 : Vector (Vector ℕ 11) 11 :=
  Specs.Poseidon.ParameterGeneration.Generated.t11.P
def S_t11 : Vector ℕ 1386 :=
  Specs.Poseidon.ParameterGeneration.Generated.t11.S

def P_t12 : Vector (Vector ℕ 12) 12 :=
  Specs.Poseidon.ParameterGeneration.Generated.t12.P
def S_t12 : Vector ℕ 1380 :=
  Specs.Poseidon.ParameterGeneration.Generated.t12.S

def P_t13 : Vector (Vector ℕ 13) 13 :=
  Specs.Poseidon.ParameterGeneration.Generated.t13.P
def S_t13 : Vector ℕ 1625 :=
  Specs.Poseidon.ParameterGeneration.Generated.t13.S

def P_t14 : Vector (Vector ℕ 14) 14 :=
  Specs.Poseidon.ParameterGeneration.Generated.t14.P
def S_t14 : Vector ℕ 1890 :=
  Specs.Poseidon.ParameterGeneration.Generated.t14.S

def P_t15 : Vector (Vector ℕ 15) 15 :=
  Specs.Poseidon.ParameterGeneration.Generated.t15.P
def S_t15 : Vector ℕ 1740 :=
  Specs.Poseidon.ParameterGeneration.Generated.t15.S

def P_t16 : Vector (Vector ℕ 16) 16 :=
  Specs.Poseidon.ParameterGeneration.Generated.t16.P
def S_t16 : Vector ℕ 1984 :=
  Specs.Poseidon.ParameterGeneration.Generated.t16.S

def P_t17 : Vector (Vector ℕ 17) 17 :=
  Specs.Poseidon.ParameterGeneration.Generated.t17.P
def S_t17 : Vector ℕ 2244 :=
  Specs.Poseidon.ParameterGeneration.Generated.t17.S

end Specs.PoseidonOptimized
