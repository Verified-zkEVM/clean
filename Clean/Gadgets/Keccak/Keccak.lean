import Mathlib.Tactic.Linarith.Frontend
import Clean.Types.U64
import Clean.Gadgets.Rotation64.Theorems
namespace Clean.Gadgets.Keccak256

open Gadgets.Rotation64.Theorems (rot_right64)

def RoundConstants : Vector ℕ 24 := #v[
  0x0000000000000001, 0x0000000000008082,
  0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088,
  0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b,
  0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080,
  0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080,
  0x0000000080000001, 0x8000000080008008
]

def bits2bytes (x : Nat) : Nat :=
  (x + 7) / 8

@[reducible]
def xor_u64 (a b : ℕ) : ℕ := a.xor b

def not_u64 (a : ℕ) : ℕ := a ^^^ 0xffffffffffffffff

def and_u64 (a b : ℕ) : ℕ := a &&& b

def rol_u64 (value : ℕ) (left : Nat) : ℕ:=
  let right := (64 - left) % 64
  rot_right64 value right


def theta_c (state : Vector ℕ 25) : Vector ℕ 5 :=
    #v[
      xor_u64 (xor_u64 (xor_u64 (xor_u64 (state.get 0) (state.get 1)) (state.get 2)) (state.get 3)) (state.get 4),
      xor_u64 (xor_u64 (xor_u64 (xor_u64 (state.get 5) (state.get 6)) (state.get 7)) (state.get 8)) (state.get 9),
      xor_u64 (xor_u64 (xor_u64 (xor_u64 (state.get 10) (state.get 11)) (state.get 12)) (state.get 13)) (state.get 14),
      xor_u64 (xor_u64 (xor_u64 (xor_u64 (state.get 15) (state.get 16)) (state.get 17)) (state.get 18)) (state.get 19),
      xor_u64 (xor_u64 (xor_u64 (xor_u64 (state.get 20) (state.get 21)) (state.get 22)) (state.get 23)) (state.get 24)
    ]

def theta_d (c : Vector ℕ 5) : Vector ℕ 5 :=
  #v[
    xor_u64 (c.get 4) (rol_u64 (c.get 1) 1),
    xor_u64 (c.get 0) (rol_u64 (c.get 2) 1),
    xor_u64 (c.get 1) (rol_u64 (c.get 3) 1),
    xor_u64 (c.get 2) (rol_u64 (c.get 4) 1),
    xor_u64 (c.get 3) (rol_u64 (c.get 0) 1)
  ]


def theta_xor (state : Vector ℕ 25) (d : Vector ℕ 5) : Vector ℕ 25 :=
  #v[
    xor_u64 (state.get 0) (d.get 0),
    xor_u64 (state.get 1) (d.get 0),
    xor_u64 (state.get 2) (d.get 0),
    xor_u64 (state.get 3) (d.get 0),
    xor_u64 (state.get 4) (d.get 0),
    xor_u64 (state.get 5) (d.get 1),
    xor_u64 (state.get 6) (d.get 1),
    xor_u64 (state.get 7) (d.get 1),
    xor_u64 (state.get 8) (d.get 1),
    xor_u64 (state.get 9) (d.get 1),
    xor_u64 (state.get 10) (d.get 2),
    xor_u64 (state.get 11) (d.get 2),
    xor_u64 (state.get 12) (d.get 2),
    xor_u64 (state.get 13) (d.get 2),
    xor_u64 (state.get 14) (d.get 2),
    xor_u64 (state.get 15) (d.get 3),
    xor_u64 (state.get 16) (d.get 3),
    xor_u64 (state.get 17) (d.get 3),
    xor_u64 (state.get 18) (d.get 3),
    xor_u64 (state.get 19) (d.get 3),
    xor_u64 (state.get 20) (d.get 4),
    xor_u64 (state.get 21) (d.get 4),
    xor_u64 (state.get 22) (d.get 4),
    xor_u64 (state.get 23) (d.get 4),
    xor_u64 (state.get 24) (d.get 4)
  ]

def theta (state : Vector ℕ 25) : Vector ℕ 25 :=
  let c := theta_c state
  let d := theta_d c
  theta_xor state d

def rho_phi (state : Vector ℕ 25) : Vector ℕ 25 :=
  #v[
    rol_u64 (state.get 0) 0,
    rol_u64 (state.get 15) 28,
    rol_u64 (state.get 5) 1,
    rol_u64 (state.get 20) 27,
    rol_u64 (state.get 10) 62,
    rol_u64 (state.get 6) 44,
    rol_u64 (state.get 21) 20,
    rol_u64 (state.get 11) 6,
    rol_u64 (state.get 1) 36,
    rol_u64 (state.get 16) 55,
    rol_u64 (state.get 12) 43,
    rol_u64 (state.get 2) 3,
    rol_u64 (state.get 17) 25,
    rol_u64 (state.get 7) 10,
    rol_u64 (state.get 22) 39,
    rol_u64 (state.get 18) 21,
    rol_u64 (state.get 8) 45,
    rol_u64 (state.get 23) 8,
    rol_u64 (state.get 13) 15,
    rol_u64 (state.get 3) 41,
    rol_u64 (state.get 24) 14,
    rol_u64 (state.get 14) 61,
    rol_u64 (state.get 4) 18,
    rol_u64 (state.get 19) 56,
    rol_u64 (state.get 9) 2
  ]

def chi (b : Vector ℕ 25) : Vector ℕ 25 :=
  #v[
    xor_u64 (b.get 0) (and_u64 (not_u64 (b.get 5)) (b.get 10)),
    xor_u64 (b.get 1) (and_u64 (not_u64 (b.get 6)) (b.get 11)),
    xor_u64 (b.get 2) (and_u64 (not_u64 (b.get 7)) (b.get 12)),
    xor_u64 (b.get 3) (and_u64 (not_u64 (b.get 8)) (b.get 13)),
    xor_u64 (b.get 4) (and_u64 (not_u64 (b.get 9)) (b.get 14)),
    xor_u64 (b.get 5) (and_u64 (not_u64 (b.get 10)) (b.get 15)),
    xor_u64 (b.get 6) (and_u64 (not_u64 (b.get 11)) (b.get 16)),
    xor_u64 (b.get 7) (and_u64 (not_u64 (b.get 12)) (b.get 17)),
    xor_u64 (b.get 8) (and_u64 (not_u64 (b.get 13)) (b.get 18)),
    xor_u64 (b.get 9) (and_u64 (not_u64 (b.get 14)) (b.get 19)),
    xor_u64 (b.get 10) (and_u64 (not_u64 (b.get 15)) (b.get 20)),
    xor_u64 (b.get 11) (and_u64 (not_u64 (b.get 16)) (b.get 21)),
    xor_u64 (b.get 12) (and_u64 (not_u64 (b.get 17)) (b.get 22)),
    xor_u64 (b.get 13) (and_u64 (not_u64 (b.get 18)) (b.get 23)),
    xor_u64 (b.get 14) (and_u64 (not_u64 (b.get 19)) (b.get 24)),
    xor_u64 (b.get 15) (and_u64 (not_u64 (b.get 20)) (b.get 0)),
    xor_u64 (b.get 16) (and_u64 (not_u64 (b.get 21)) (b.get 1)),
    xor_u64 (b.get 17) (and_u64 (not_u64 (b.get 22)) (b.get 2)),
    xor_u64 (b.get 18) (and_u64 (not_u64 (b.get 23)) (b.get 3)),
    xor_u64 (b.get 19) (and_u64 (not_u64 (b.get 24)) (b.get 4)),
    xor_u64 (b.get 20) (and_u64 (not_u64 (b.get 0)) (b.get 5)),
    xor_u64 (b.get 21) (and_u64 (not_u64 (b.get 1)) (b.get 6)),
    xor_u64 (b.get 22) (and_u64 (not_u64 (b.get 2)) (b.get 7)),
    xor_u64 (b.get 23) (and_u64 (not_u64 (b.get 3)) (b.get 8)),
    xor_u64 (b.get 24) (and_u64 (not_u64 (b.get 4)) (b.get 9))
  ]

def iota (state : Vector ℕ 25) (rc : ℕ) : Vector ℕ 25 :=
  state.set 0 (xor_u64 rc <| state.get 0)


def keccak_round (state : Vector ℕ 25) (rc : ℕ) : Vector ℕ 25 :=
  let theta_state := theta state
  let rho_phi_state := rho_phi theta_state
  let chi_state := chi rho_phi_state
  iota chi_state rc

def keccak_f (state : Vector ℕ 25): Vector ℕ 25 :=
  let rec keccak_f_aux (state : Vector ℕ 25) (i : ℕ) : Vector ℕ 25 :=
    match i with
    | 0 => state
    | i + 1 =>
      let state' := keccak_f_aux state i
      (keccak_round state' (RoundConstants.get i))

  keccak_f_aux state 24

end Clean.Gadgets.Keccak256

namespace Clean.Gadgets.Keccak256.Tests
-- ============= Testing =============

def state : Vector (U64 ℕ) 25 := #v[
  ⟨67, 168, 144, 181, 2, 173, 144, 47⟩,
  ⟨114, 52, 107, 105, 171, 22, 114, 75⟩,
  ⟨196, 118, 22, 253, 100, 162, 87, 52⟩,
  ⟨50, 65, 171, 81, 229, 6, 172, 155⟩,
  ⟨178, 167, 68, 225, 82, 73, 216, 194⟩,
  ⟨193, 5, 52, 193, 148, 168, 64, 147⟩,
  ⟨212, 142, 107, 244, 55, 237, 100, 203⟩,
  ⟨101, 34, 195, 62, 133, 216, 64, 34⟩,
  ⟨240, 214, 204, 27, 17, 231, 66, 179⟩,
  ⟨136, 37, 228, 137, 64, 208, 27, 90⟩,
  ⟨177, 229, 130, 4, 191, 7, 25, 117⟩,
  ⟨124, 168, 245, 7, 222, 138, 168, 16⟩,
  ⟨115, 130, 213, 74, 217, 123, 172, 109⟩,
  ⟨128, 149, 137, 6, 45, 133, 77, 101⟩,
  ⟨104, 90, 153, 237, 72, 44, 164, 84⟩,
  ⟨129, 177, 235, 28, 82, 30, 150, 201⟩,
  ⟨52, 55, 32, 241, 142, 211, 246, 68⟩,
  ⟨149, 124, 124, 204, 34, 220, 229, 69⟩,
  ⟨215, 168, 47, 96, 70, 5, 220, 2⟩,
  ⟨53, 224, 38, 18, 110, 66, 70, 9⟩,
  ⟨213, 122, 200, 196, 186, 122, 207, 42⟩,
  ⟨141, 103, 32, 88, 244, 160, 37, 76⟩,
  ⟨99, 242, 138, 24, 4, 30, 100, 196⟩,
  ⟨141, 253, 136, 54, 8, 21, 204, 152⟩,
  ⟨93, 161, 29, 12, 44, 252, 49, 57⟩
]
-- state = [[67, 168, 144, 181, 2, 173, 144, 47], [114, 52, 107, 105, 171, 22, 114, 75], [196, 118, 22, 253, 100, 162, 87, 52], [50, 65, 171, 81, 229, 6, 172, 155], [178, 167, 68, 225, 82, 73, 216, 194], [193, 5, 52, 193, 148, 168, 64, 147], [212, 142, 107, 244, 55, 237, 100, 203], [101, 34, 195, 62, 133, 216, 64, 34], [240, 214, 204, 27, 17, 231, 66, 179], [136, 37, 228, 137, 64, 208, 27, 90], [177, 229, 130, 4, 191, 7, 25, 117], [124, 168, 245, 7, 222, 138, 168, 16], [115, 130, 213, 74, 217, 123, 172, 109], [128, 149, 137, 6, 45, 133, 77, 101], [104, 90, 153, 237, 72, 44, 164, 84], [129, 177, 235, 28, 82, 30, 150, 201], [52, 55, 32, 241, 142, 211, 246, 68], [149, 124, 124, 204, 34, 220, 229, 69], [215, 168, 47, 96, 70, 5, 220, 2], [53, 224, 38, 18, 110, 66, 70, 9], [213, 122, 200, 196, 186, 122, 207, 42], [141, 103, 32, 88, 244, 160, 37, 76], [99, 242, 138, 24, 4, 30, 100, 196], [141, 253, 136, 54, 8, 21, 204, 152], [93, 161, 29, 12, 44, 252, 49, 57]]

def state' := state.map (λ x => x |> U64.value_nat)

def rc : U64 ℕ := ⟨235, 226, 178, 113, 2, 17, 87, 249⟩
#eval theta state' |> rho_phi |> chi
#eval keccak_f state' |>.map (λ x => x |> U64.decompose_nat_nat)
-- [[158, 112, 239, 65, 247, 184, 42, 29],[18, 33, 104, 153, 4, 113, 230, 164], [203, 128, 138, 52, 66, 249, 134, 137], [204, 130, 87, 203, 75, 229, 26, 49], [101, 124, 134, 181, 193, 247, 248, 194], [170, 160, 115, 17, 65, 59, 26, 242], [211, 14, 202, 60, 11, 138, 72, 44], [21, 90, 64, 58, 127, 167, 131, 94], [242, 160, 171, 170, 232, 135, 11, 166], [172, 234, 194, 74, 41, 176, 182, 229], [174, 35, 251, 95, 139, 151, 128, 196], [140, 76, 0, 166, 43, 181, 26, 214], [15, 95, 132, 163, 192, 11, 248, 213], [99, 110, 8, 73, 127, 107, 70, 240], [208, 251, 207, 18, 172, 113, 72, 220], [166, 119, 55, 190, 184, 224, 76, 193], [132, 182, 193, 105, 46, 92, 159, 3], [161, 219, 100, 118, 249, 82, 69, 168], [3, 191, 204, 13, 134, 22, 134, 93], [250, 46, 70, 133, 112, 75, 14, 27], [230, 133, 192, 229, 9, 245, 148, 47], [41, 51, 79, 61, 157, 210, 157, 201], [81, 88, 205, 113, 250, 141, 5, 116], [137, 227, 13, 73, 228, 151, 175, 151], [62, 184, 103, 254, 5, 201, 102, 121]]

end Clean.Gadgets.Keccak256.Tests
