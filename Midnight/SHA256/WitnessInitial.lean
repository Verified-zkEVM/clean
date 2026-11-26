import Midnight.SHA256.Semantics.Preimage

/-! Constructive initial environment for the pinned preimage example. Only its
public digest, external hint and five source table columns are initialized here;
the witness executor subsequently writes the source advice/fixed assignments. -/
namespace Midnight.SHA256.WitnessInitial
open Halo2 Semantics

attribute [local irreducible] Spec.digest Preimage.hintMessage

def tableValues : Nat → List F
  | 11 => byteRangeRows.map fun row => (row.1 : F)
  | 12 => byteRangeRows.map fun row => (row.2 : F)
  | 13 => spreadRows.map fun row => (row.1 : F)
  | 14 => spreadRows.map fun row => (row.2.1 : F)
  | 15 => spreadRows.map fun row => (row.2.2 : F)
  | _ => []

/-- Source table default-fill is the first row, including all unused usable rows. -/
def tableAt (column : Nat) (row : Int) : F :=
  if row < 0 then 0 else
    let values := tableValues column
    if row.toNat < values.length then values[row.toNat]! else values[0]!

/-- Exactly the pinned native k=13 usable domain (8192 minus nine reserved rows). -/
def initial (hint : ProverHint F) : ProverEnvironment F where
  get column row := match column.kind with
    | .fixed => tableAt column.index row
    | .advice => 0
    | .instance => if column.index = 1 ∧ 0 ≤ row ∧ row.toNat < 32 then
        ((Spec.digest (Preimage.hintMessage hint)).toArray[row.toNat]! : F) else 0
  usableRows := 8183
  hint := hint

attribute [local irreducible] initial Preimage.publicDigest

@[simp] theorem initial_hint (hint : ProverHint F) : (initial hint).hint = hint := by unfold initial; rfl
@[simp] theorem initial_usableRows (hint : ProverHint F) : (initial hint).usableRows = 8183 := by unfold initial; rfl

theorem fixed_at_nat (hint : ProverHint F) (column row : Nat) :
    (initial hint).toEnvironment.fixed ⟨column⟩ (row : Int) =
      if row < (tableValues column).length then (tableValues column)[row]!
      else (tableValues column)[0]! := by
  simp only [initial, Environment.fixed, Column.toAny, tableAt, Int.natCast_nonneg, not_lt_of_ge,
    ↓reduceIte, Int.toNat_natCast]

theorem columnLoaded (hint : ProverHint F) (column : Nat) :
    ColumnLoaded (initial hint).toEnvironment ⟨column⟩ (tableValues column) := by
  constructor
  · intro row bound
    rw [fixed_at_nat, ite_eq_left bound]
  · intro _ row bound _
    rw [fixed_at_nat, ite_eq_right (Nat.not_lt.mpr bound)]

theorem range_length : byteRangeRows.length = 257 := by decide +kernel

theorem spread_length : spreadRows.length = 7933 := by
  simp [spreadRows, spreadWidths]

theorem capacity (hint : ProverHint F) : Preimage.Capacity (initial hint).toEnvironment := by
  unfold Preimage.Capacity
  rw [initial_usableRows]
  rw [range_length, spread_length]
  decide

/-- All five actual tail loads hold in the explicit initial environment,
independently of placement and starting region index. -/
theorem tables_witnesses (hint : ProverHint F) (place : RegionIndex → Nat) (self : RegionIndex) :
    ExtendsWitnesses place (initial hint) (Preimage.tables.operations self) self := by
  have c11 := columnLoaded hint 11
  have c12 := columnLoaded hint 12
  have c13 := columnLoaded hint 13
  have c14 := columnLoaded hint 14
  have c15 := columnLoaded hint 15
  simp only [Preimage.tables, shaTables, circuit_norm]
  exact ⟨c11.entries,c11.fill,c12.entries,c12.fill,c13.entries,c13.fill,
    c14.entries,c14.fill,c15.entries,c15.fill⟩

theorem instance_at (hint : ProverHint F) (i : Fin 32) :
    (initial hint).toEnvironment.inst ⟨1⟩ i.val =
      ((Spec.digest (Preimage.hintMessage hint))[i] : F) := by
  simp only [initial, Environment.inst, Int.natCast_nonneg, Int.toNat_natCast,
    i.isLt, and_self, Fin.getElem_fin]
  rw [getElem!_pos _ i.val (by simp)]
  rfl

private theorem publicDigest_of_instances (env : Environment F) (digest : Vector Nat 32)
    (bounded : ∀ i : Fin 32, digest[i] < BLS12_381.scalarFieldSize)
    (instances : ∀ i : Fin 32, env.inst ⟨1⟩ i.val = (digest[i] : F)) :
    Preimage.publicDigest env = digest := by
  unfold Preimage.publicDigest
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  have bound := bounded ⟨i,hi⟩
  have valueAt := congrArg ZMod.val (instances ⟨i,hi⟩)
  simp only [Fin.getElem_fin, ZMod.val_natCast] at valueAt bound
  rw [Nat.mod_eq_of_lt bound] at valueAt
  exact valueAt

/-- The initial instance statement is the honest message's actual SHA digest. -/
theorem public_digest (hint : ProverHint F) :
    Preimage.publicDigest (initial hint).toEnvironment = Spec.digest (Preimage.hintMessage hint) := by
  apply publicDigest_of_instances (initial hint).toEnvironment
    (Spec.digest (Preimage.hintMessage hint))
  · intro i
    exact (Spec.digest_byte_lt (Preimage.hintMessage hint) i).trans
      (by norm_num [BLS12_381.scalarFieldSize])
  · exact instance_at hint

/-- Encode any 24-byte message as the fixed external hint interface. Every
other hint query returns an empty row array. -/
def hintFor (message : Spec.Message) : ProverHint F := fun key count =>
  if key = Preimage.hintKey ∧ count = 24 then
    #[Vector.ofFn fun i => (message.toArray[i.val]! : F)] else #[]

theorem hintFor_message (message : Spec.Message) (bytes : Spec.Bytes message) :
    Preimage.hintMessage (hintFor message) = message := by
  unfold Preimage.hintMessage
  apply Vector.ext
  intro i hi
  have bound : message[i] < BLS12_381.scalarFieldSize :=
    (bytes ⟨i,hi⟩).trans (by norm_num [BLS12_381.scalarFieldSize])
  simp only [Preimage.hintFields, hintFor, and_self, ↓reduceIte, Array.getElem?_eq_getElem,
    Array.size_singleton, Nat.zero_lt_succ, Array.getElem_singleton, Option.getD_some,
    Vector.getElem_map, Vector.getElem_ofFn, getElem!_pos message.toArray i (by simpa using hi),
    ZMod.val_natCast, Vector.getElem_toArray, Nat.mod_eq_of_lt bound]

end Midnight.SHA256.WitnessInitial
