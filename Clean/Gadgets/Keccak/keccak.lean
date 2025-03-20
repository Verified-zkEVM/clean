import Mathlib.Tactic.Linarith.Frontend
import Clean.Types.U64


def RoundConstants : List (U64 ℕ) := [
    ⟨1, 0, 0, 0, 0, 0, 0, 0⟩,
    ⟨130, 128, 0, 0, 0, 0, 0, 0⟩,
    ⟨138, 128, 0, 0, 0, 0, 0, 128⟩,
    ⟨0, 128, 0, 128, 0, 0, 0, 128⟩,
    ⟨139, 128, 0, 0, 0, 0, 0, 0⟩,
    ⟨1, 0, 0, 128, 0, 0, 0, 0⟩,
    ⟨129, 128, 0, 128, 0, 0, 0, 128⟩,
    ⟨9, 128, 0, 0, 0, 0, 0, 128⟩,
    ⟨138, 0, 0, 0, 0, 0, 0, 0⟩,
    ⟨136, 0, 0, 0, 0, 0, 0, 0⟩,
    ⟨9, 128, 0, 128, 0, 0, 0, 0⟩,
    ⟨10, 0, 0, 128, 0, 0, 0, 0⟩,
    ⟨139, 128, 0, 128, 0, 0, 0, 0⟩,
    ⟨139, 0, 0, 0, 0, 0, 0, 128⟩,
    ⟨137, 128, 0, 0, 0, 0, 0, 128⟩,
    ⟨3, 128, 0, 0, 0, 0, 0, 128⟩,
    ⟨2, 128, 0, 0, 0, 0, 0, 128⟩,
    ⟨128, 0, 0, 0, 0, 0, 0, 128⟩,
    ⟨10, 128, 0, 0, 0, 0, 0, 0⟩,
    ⟨10, 0, 0, 128, 0, 0, 0, 128⟩,
    ⟨129, 128, 0, 128, 0, 0, 0, 128⟩,
    ⟨128, 128, 0, 0, 0, 0, 0, 128⟩,
    ⟨1, 0, 0, 128, 0, 0, 0, 0⟩,
    ⟨8, 128, 0, 128, 0, 0, 0, 128⟩,
]

def bits2bytes (x : Nat) : Nat :=
  (x + 7) / 8

def zero_u64 : U64 ℕ :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

def xor_u64 (a b : U64 ℕ) : U64 ℕ :=
  ⟨
    Nat.xor a.x0 b.x0,
    Nat.xor a.x1 b.x1,
    Nat.xor a.x2 b.x2,
    Nat.xor a.x3 b.x3,
    Nat.xor a.x4 b.x4,
    Nat.xor a.x5 b.x5,
    Nat.xor a.x6 b.x6,
    Nat.xor a.x7 b.x7
  ⟩

def not_u64 (a : U64 ℕ) : U64 ℕ :=
  ⟨
    Nat.xor 0xff a.x0,
    Nat.xor 0xff a.x1,
    Nat.xor 0xff a.x2,
    Nat.xor 0xff a.x3,
    Nat.xor 0xff a.x4,
    Nat.xor 0xff a.x5,
    Nat.xor 0xff a.x6,
    Nat.xor 0xff a.x7
  ⟩

def and_u64 (a b : U64 ℕ) : U64 ℕ :=
  ⟨
    Nat.land a.x0 b.x0,
    Nat.land a.x1 b.x1,
    Nat.land a.x2 b.x2,
    Nat.land a.x3 b.x3,
    Nat.land a.x4 b.x4,
    Nat.land a.x5 b.x5,
    Nat.land a.x6 b.x6,
    Nat.land a.x7 b.x7
  ⟩

def rol_u64 (value : U64 ℕ) (left : Nat) : U64 ℕ:=
  let value : ℕ := value.value_nat
  let left := (64 - left) % 64
  let low := value % (2^left)
  let high := value / (2^left)
  let low := low * (2^(64 - left))
  let res := low + high
  U64.decompose_nat_nat res


#eval rol_u64 ⟨235, 226, 178, 113, 2, 17, 87, 249⟩ 63

def theta_c (state : List (U64 ℕ)) : List (U64 ℕ) :=
    [
      xor_u64 (xor_u64 (xor_u64 (xor_u64 (state.getD 0 zero_u64) (state.getD 1 zero_u64)) (state.getD 2 zero_u64)) (state.getD 3 zero_u64)) (state.getD 4 zero_u64),
      xor_u64 (xor_u64 (xor_u64 (xor_u64 (state.getD 5 zero_u64) (state.getD 6 zero_u64)) (state.getD 7 zero_u64)) (state.getD 8 zero_u64)) (state.getD 9 zero_u64),
      xor_u64 (xor_u64 (xor_u64 (xor_u64 (state.getD 10 zero_u64) (state.getD 11 zero_u64)) (state.getD 12 zero_u64)) (state.getD 13 zero_u64)) (state.getD 14 zero_u64),
      xor_u64 (xor_u64 (xor_u64 (xor_u64 (state.getD 15 zero_u64) (state.getD 16 zero_u64)) (state.getD 17 zero_u64)) (state.getD 18 zero_u64)) (state.getD 19 zero_u64),
      xor_u64 (xor_u64 (xor_u64 (xor_u64 (state.getD 20 zero_u64) (state.getD 21 zero_u64)) (state.getD 22 zero_u64)) (state.getD 23 zero_u64)) (state.getD 24 zero_u64)
    ]

def theta_d (c : List (U64 ℕ)) : List (U64 ℕ) :=
  [
    xor_u64 (c.getD 4 zero_u64) (rol_u64 (c.getD 1 zero_u64) 1),
    xor_u64 (c.getD 0 zero_u64) (rol_u64 (c.getD 2 zero_u64) 1),
    xor_u64 (c.getD 1 zero_u64) (rol_u64 (c.getD 3 zero_u64) 1),
    xor_u64 (c.getD 2 zero_u64) (rol_u64 (c.getD 4 zero_u64) 1),
    xor_u64 (c.getD 3 zero_u64) (rol_u64 (c.getD 0 zero_u64) 1)
  ]


def theta_xor (state : List (U64 ℕ)) (d : List (U64 ℕ)) : List (U64 ℕ) :=
  [
    xor_u64 (state.getD 0 zero_u64) (d.getD 0 zero_u64),
    xor_u64 (state.getD 1 zero_u64) (d.getD 0 zero_u64),
    xor_u64 (state.getD 2 zero_u64) (d.getD 0 zero_u64),
    xor_u64 (state.getD 3 zero_u64) (d.getD 0 zero_u64),
    xor_u64 (state.getD 4 zero_u64) (d.getD 0 zero_u64),
    xor_u64 (state.getD 5 zero_u64) (d.getD 1 zero_u64),
    xor_u64 (state.getD 6 zero_u64) (d.getD 1 zero_u64),
    xor_u64 (state.getD 7 zero_u64) (d.getD 1 zero_u64),
    xor_u64 (state.getD 8 zero_u64) (d.getD 1 zero_u64),
    xor_u64 (state.getD 9 zero_u64) (d.getD 1 zero_u64),
    xor_u64 (state.getD 10 zero_u64) (d.getD 2 zero_u64),
    xor_u64 (state.getD 11 zero_u64) (d.getD 2 zero_u64),
    xor_u64 (state.getD 12 zero_u64) (d.getD 2 zero_u64),
    xor_u64 (state.getD 13 zero_u64) (d.getD 2 zero_u64),
    xor_u64 (state.getD 14 zero_u64) (d.getD 2 zero_u64),
    xor_u64 (state.getD 15 zero_u64) (d.getD 3 zero_u64),
    xor_u64 (state.getD 16 zero_u64) (d.getD 3 zero_u64),
    xor_u64 (state.getD 17 zero_u64) (d.getD 3 zero_u64),
    xor_u64 (state.getD 18 zero_u64) (d.getD 3 zero_u64),
    xor_u64 (state.getD 19 zero_u64) (d.getD 3 zero_u64),
    xor_u64 (state.getD 20 zero_u64) (d.getD 4 zero_u64),
    xor_u64 (state.getD 21 zero_u64) (d.getD 4 zero_u64),
    xor_u64 (state.getD 22 zero_u64) (d.getD 4 zero_u64),
    xor_u64 (state.getD 23 zero_u64) (d.getD 4 zero_u64),
    xor_u64 (state.getD 24 zero_u64) (d.getD 4 zero_u64)
  ]

def theta (state : List (U64 ℕ)) : List (U64 ℕ) :=
  let c := theta_c state
  let d := theta_d c
  theta_xor state d

def rho_phi (state : List (U64 ℕ)) : List (U64 ℕ) :=
  [
    rol_u64 (state.getD 0 zero_u64) 0,
    rol_u64 (state.getD 15 zero_u64) 28,
    rol_u64 (state.getD 5 zero_u64) 1,
    rol_u64 (state.getD 20 zero_u64) 27,
    rol_u64 (state.getD 10 zero_u64) 62,
    rol_u64 (state.getD 6 zero_u64) 44,
    rol_u64 (state.getD 21 zero_u64) 20,
    rol_u64 (state.getD 11 zero_u64) 6,
    rol_u64 (state.getD 1 zero_u64) 36,
    rol_u64 (state.getD 16 zero_u64) 55,
    rol_u64 (state.getD 12 zero_u64) 43,
    rol_u64 (state.getD 2 zero_u64) 3,
    rol_u64 (state.getD 17 zero_u64) 25,
    rol_u64 (state.getD 7 zero_u64) 10,
    rol_u64 (state.getD 22 zero_u64) 39,
    rol_u64 (state.getD 18 zero_u64) 21,
    rol_u64 (state.getD 8 zero_u64) 45,
    rol_u64 (state.getD 23 zero_u64) 8,
    rol_u64 (state.getD 13 zero_u64) 15,
    rol_u64 (state.getD 3 zero_u64) 41,
    rol_u64 (state.getD 24 zero_u64) 14,
    rol_u64 (state.getD 14 zero_u64) 61,
    rol_u64 (state.getD 4 zero_u64) 18,
    rol_u64 (state.getD 19 zero_u64) 56,
    rol_u64 (state.getD 9 zero_u64) 2
  ]

def chi (b : List (U64 ℕ)) : List (U64 ℕ) :=
  [
    xor_u64 (b.getD 0 zero_u64) (and_u64 (not_u64 (b.getD 5 zero_u64)) (b.getD 10 zero_u64)),
    xor_u64 (b.getD 1 zero_u64) (and_u64 (not_u64 (b.getD 6 zero_u64)) (b.getD 11 zero_u64)),
    xor_u64 (b.getD 2 zero_u64) (and_u64 (not_u64 (b.getD 7 zero_u64)) (b.getD 12 zero_u64)),
    xor_u64 (b.getD 3 zero_u64) (and_u64 (not_u64 (b.getD 8 zero_u64)) (b.getD 13 zero_u64)),
    xor_u64 (b.getD 4 zero_u64) (and_u64 (not_u64 (b.getD 9 zero_u64)) (b.getD 14 zero_u64)),
    xor_u64 (b.getD 5 zero_u64) (and_u64 (not_u64 (b.getD 10 zero_u64)) (b.getD 15 zero_u64)),
    xor_u64 (b.getD 6 zero_u64) (and_u64 (not_u64 (b.getD 11 zero_u64)) (b.getD 16 zero_u64)),
    xor_u64 (b.getD 7 zero_u64) (and_u64 (not_u64 (b.getD 12 zero_u64)) (b.getD 17 zero_u64)),
    xor_u64 (b.getD 8 zero_u64) (and_u64 (not_u64 (b.getD 13 zero_u64)) (b.getD 18 zero_u64)),
    xor_u64 (b.getD 9 zero_u64) (and_u64 (not_u64 (b.getD 14 zero_u64)) (b.getD 19 zero_u64)),
    xor_u64 (b.getD 10 zero_u64) (and_u64 (not_u64 (b.getD 15 zero_u64)) (b.getD 20 zero_u64)),
    xor_u64 (b.getD 11 zero_u64) (and_u64 (not_u64 (b.getD 16 zero_u64)) (b.getD 21 zero_u64)),
    xor_u64 (b.getD 12 zero_u64) (and_u64 (not_u64 (b.getD 17 zero_u64)) (b.getD 22 zero_u64)),
    xor_u64 (b.getD 13 zero_u64) (and_u64 (not_u64 (b.getD 18 zero_u64)) (b.getD 23 zero_u64)),
    xor_u64 (b.getD 14 zero_u64) (and_u64 (not_u64 (b.getD 19 zero_u64)) (b.getD 24 zero_u64)),
    xor_u64 (b.getD 15 zero_u64) (and_u64 (not_u64 (b.getD 20 zero_u64)) (b.getD 0 zero_u64)),
    xor_u64 (b.getD 16 zero_u64) (and_u64 (not_u64 (b.getD 21 zero_u64)) (b.getD 1 zero_u64)),
    xor_u64 (b.getD 17 zero_u64) (and_u64 (not_u64 (b.getD 22 zero_u64)) (b.getD 2 zero_u64)),
    xor_u64 (b.getD 18 zero_u64) (and_u64 (not_u64 (b.getD 23 zero_u64)) (b.getD 3 zero_u64)),
    xor_u64 (b.getD 19 zero_u64) (and_u64 (not_u64 (b.getD 24 zero_u64)) (b.getD 4 zero_u64)),
    xor_u64 (b.getD 20 zero_u64) (and_u64 (not_u64 (b.getD 0 zero_u64)) (b.getD 5 zero_u64)),
    xor_u64 (b.getD 21 zero_u64) (and_u64 (not_u64 (b.getD 1 zero_u64)) (b.getD 6 zero_u64)),
    xor_u64 (b.getD 22 zero_u64) (and_u64 (not_u64 (b.getD 2 zero_u64)) (b.getD 7 zero_u64)),
    xor_u64 (b.getD 23 zero_u64) (and_u64 (not_u64 (b.getD 3 zero_u64)) (b.getD 8 zero_u64)),
    xor_u64 (b.getD 24 zero_u64) (and_u64 (not_u64 (b.getD 4 zero_u64)) (b.getD 9 zero_u64))
  ]

def iota (state : List (U64 ℕ)) (rc : U64 ℕ) : List (U64 ℕ) :=
  match state with
  | [] => []
  | h :: t => xor_u64 h rc :: t


def keccak_round (state : List (U64 ℕ)) (rc : U64 ℕ) : List (U64 ℕ) :=
  let theta_state := theta state
  let rho_phi_state := rho_phi theta_state
  let chi_state := chi rho_phi_state
  iota chi_state rc

def keccak_f (state : List (U64 ℕ)): List (U64 ℕ) :=
  let rec keccak_f_aux (state : List (U64 ℕ)) (i : ℕ) : List (U64 ℕ) :=
    match i with
    | 0 => state
    | i + 1 =>
      let state' := keccak_f_aux state i
      (keccak_round state' (RoundConstants.getD i zero_u64))

  keccak_f_aux state 24


-- ============= Testing =============

def state : List (U64 ℕ) :=[
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


def rc : U64 ℕ := ⟨235, 226, 178, 113, 2, 17, 87, 249⟩
#eval theta state |> rho_phi |> chi
#eval keccak_f state
-- [[158, 112, 239, 65, 247, 184, 42, 29],[18, 33, 104, 153, 4, 113, 230, 164], [203, 128, 138, 52, 66, 249, 134, 137], [204, 130, 87, 203, 75, 229, 26, 49], [101, 124, 134, 181, 193, 247, 248, 194], [170, 160, 115, 17, 65, 59, 26, 242], [211, 14, 202, 60, 11, 138, 72, 44], [21, 90, 64, 58, 127, 167, 131, 94], [242, 160, 171, 170, 232, 135, 11, 166], [172, 234, 194, 74, 41, 176, 182, 229], [174, 35, 251, 95, 139, 151, 128, 196], [140, 76, 0, 166, 43, 181, 26, 214], [15, 95, 132, 163, 192, 11, 248, 213], [99, 110, 8, 73, 127, 107, 70, 240], [208, 251, 207, 18, 172, 113, 72, 220], [166, 119, 55, 190, 184, 224, 76, 193], [132, 182, 193, 105, 46, 92, 159, 3], [161, 219, 100, 118, 249, 82, 69, 168], [3, 191, 204, 13, 134, 22, 134, 93], [250, 46, 70, 133, 112, 75, 14, 27], [230, 133, 192, 229, 9, 245, 148, 47], [41, 51, 79, 61, 157, 210, 157, 201], [81, 88, 205, 113, 250, 141, 5, 116], [137, 227, 13, 73, 228, 151, 175, 151], [62, 184, 103, 254, 5, 201, 102, 121]]
