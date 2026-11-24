import Midnight.Field
import Clean.Halo2.Keygen.FloorPlanner.Simple
import Clean.Halo2.Keygen.Layout
import Midnight.Chips.LayoutLawful
import Midnight.Chips.CopyLawful
import Midnight.Chips.Planner
import Clean.Halo2.Compiler.CompiledCopies

namespace Midnight.Chips.Layout
open Halo2

structure DerivedLayout where
  regionStarts : List Nat
  copies : List (Nat × Nat × Nat × Nat)
  fixed : Array (Array Nat)
  selectorRows : Array (Array Nat)

/-- Allocation counts before selectors become additional fixed columns. -/
structure Config where
  numAdvice : Nat
  numFixed : Nat
  numInstance : Nat
  numSelectors : Nat
  blindingFactors : Nat
  k : Nat
  /-- `constants[0]`, the only constants column Rust's Simple planner fills. -/
  constant : Option Nat := none

def Config.rows (config : Config) : Nat := 2 ^ config.k
def Config.usableRows (config : Config) : Nat := config.rows - config.blindingFactors - 1

/-- Use the selected planner's actual copy extractor: Simple flushes each region's constants
copies after its equality and instance copies, V1 all of them after synthesis (v1.rs:118-138). -/
def Planner.copyList (planner : Planner) (permutation : List Halo2.Layout.ColRef)
    (starts : List Nat) (constant : Option Nat) (ops : Operations F) : List CopyLawful.ResolvedCopy :=
  match planner with
  | .simple => Halo2.Layout.SimpleFloorPlanner.copyList permutation starts ops
      (Planner.simple.constants constant ops)
  | .v1 columns => Halo2.Layout.V1.copyList permutation starts ops
      ((Planner.v1 columns).constants constant ops)

/-- Keygen's fixed writes in Rust's stream order (`Assembly::assign_fixed` keeps the last,
keygen.rs:116-174): a region's `assign_fixed`s, then its constants (single_pass.rs:198-222); a
table's cells, then its default fill. `constants` is the planner's allocation, region by region;
V1 writes all of them after synthesis (`sourceFixedWrites`). -/
def streamFixedWrites (usable : Nat) (starts : List Nat) :
    List (Nat × Nat × Nat) → Nat → Operations F → List LayoutLawful.Write
  | _, _, [] => []
  | constants, index, .region _ body :: rest =>
      let count := (FloorPlanner.regionConstantValues body).length
      Halo2.Layout.regionAssignFixed scalarNat starts [(index, body)] ++
        Halo2.Layout.constantsFixed (constants.take count) ++
        streamFixedWrites usable starts (constants.drop count) (index + 1) rest
  | constants, index, .loadTable table values :: rest =>
      Halo2.Layout.tableFixed scalarNat usable [.loadTable table values] ++
        streamFixedWrites usable starts constants index rest
  | constants, index, .constrainInstance _ _ _ :: rest =>
      streamFixedWrites usable starts constants index rest

def sourceFixedWrites (ops : Operations F) (config : Config) (planner : Planner := .simple) : List LayoutLawful.Write :=
  match planner with
  | .simple => streamFixedWrites config.usableRows (Planner.simple.starts config.constant ops)
      (Planner.simple.constants config.constant ops) 0 ops
  | .v1 columns => streamFixedWrites config.usableRows ((Planner.v1 columns).starts config.constant ops) [] 0 ops ++
      Halo2.Layout.constantsFixed ((Planner.v1 columns).constants config.constant ops)

def sourceActivations (ops : Operations F) (constant : Option Nat) (planner : Planner := .simple) :
    List (Nat × Nat) :=
  Halo2.activations (planner.starts constant ops) (indexedRegions ops 0).1

theorem mem_streamFixedWrites {usable : Nat} {starts : List Nat} {write : LayoutLawful.Write}
    (ops : Operations F) : ∀ (constants : List (Nat × Nat × Nat)) (index : Nat),
    write ∈ streamFixedWrites usable starts constants index ops →
      write ∈ Halo2.Layout.constantsFixed constants ∨
        write ∈ Halo2.Layout.tableFixed scalarNat usable ops ∨
        write ∈ Halo2.Layout.regionAssignFixed scalarNat starts (indexedRegions ops index).1 := by
  induction ops with
  | nil => intro constants index member; simp [streamFixedWrites] at member
  | cons op rest ih =>
    intro constants index member
    cases op with
    | region name body =>
      simp only [streamFixedWrites, List.mem_append] at member
      rcases member with (here | constant) | later
      · right; right
        simp only [indexedRegions, Halo2.Layout.regionAssignFixed, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.mem_append] at here ⊢
        exact Or.inl here
      · left
        simp only [Halo2.Layout.constantsFixed, List.mem_map] at constant ⊢
        obtain ⟨entry, taken, equal⟩ := constant
        exact ⟨entry, List.mem_of_mem_take taken, equal⟩
      · rcases ih _ _ later with constant | table | region
        · left
          simp only [Halo2.Layout.constantsFixed, List.mem_map] at constant ⊢
          obtain ⟨entry, dropped, equal⟩ := constant
          exact ⟨entry, List.mem_of_mem_drop dropped, equal⟩
        · right; left
          simpa only [Halo2.Layout.tableFixed] using table
        · right; right
          simp only [indexedRegions, Halo2.Layout.regionAssignFixed, List.flatMap_cons,
            List.mem_append] at region ⊢
          exact Or.inr region
    | loadTable table values =>
      simp only [streamFixedWrites, List.mem_append] at member
      rcases member with here | later
      · right; left
        simp only [Halo2.Layout.tableFixed, List.append_nil, List.mem_append] at here ⊢
        exact Or.inl here
      · rcases ih _ _ later with constant | table | region
        · exact Or.inl constant
        · right; left
          simp only [Halo2.Layout.tableFixed, List.mem_append]
          exact Or.inr table
        · right; right
          simpa only [indexedRegions] using region
    | constrainInstance cell column row =>
      simp only [streamFixedWrites] at member
      rcases ih _ _ member with constant | table | region
      · exact Or.inl constant
      · right; left
        simpa only [Halo2.Layout.tableFixed] using table
      · right; right
        simpa only [indexedRegions] using region

/-- Without a constants column every fixed write is a table's or a region's. -/
theorem mem_sourceFixedWrites_none {ops : Operations F} {config : Config}
    (absent : config.constant = none) {write : LayoutLawful.Write}
    (member : write ∈ sourceFixedWrites ops config .simple) :
    write ∈ Halo2.Layout.tableFixed scalarNat config.usableRows ops ++
      Halo2.Layout.regionAssignFixed scalarNat (simpleStarts ops) (indexedRegions ops 0).1 := by
  change write ∈ streamFixedWrites config.usableRows (Planner.simple.starts config.constant ops)
    (Planner.simple.constants config.constant ops) 0 ops at member
  rw [absent] at member
  rcases mem_streamFixedWrites ops _ _ member with constant | table | region
  · simp [Halo2.Layout.constantsFixed, Planner.constants] at constant
  · exact List.mem_append_left _ table
  · exact List.mem_append_right _ region

/-- Proof-carrying fixed/selector compilation of this exact source stream.
Copy provenance and gate registration are composed separately by CertifiedCircuit. -/
structure CertifiedLayout (ops : Operations F) (permutationColumns : List Halo2.Layout.ColRef)
    (config : Config) (planner : Planner := .simple) : Type where
  fixedCertificate : LayoutLawful.CertifiedFixed config.rows config.usableRows
    config.numFixed config.numSelectors (sourceFixedWrites ops config planner) (sourceActivations ops config.constant planner)

/-- The layout keys are derived from: the source stream's region starts, copies, dense fixed
matrix (selector columns included) and selector rows. It needs no certificate; `KeyChecks`
compares Rust's `usize` layout with it. -/
def derivedLayout (ops : Operations F) (permutationColumns : List Halo2.Layout.ColRef)
    (config : Config) (planner : Planner := .simple) : DerivedLayout :=
  let fixed := (LayoutLawful.dense config.rows (config.numFixed + config.numSelectors)
    (sourceFixedWrites ops config planner ++ LayoutLawful.selectorWrites config.numFixed
      (sourceActivations ops config.constant planner))).toArray.map List.toArray
  let selectorRows := (Array.range config.numSelectors).map fun selector =>
    (Array.range config.rows).filter fun row =>
      ((fixed[config.numFixed + selector]?.bind fun values => values[row]?).getD 0) == 1
  { regionStarts := planner.starts config.constant ops
    copies := planner.copyList permutationColumns (planner.starts config.constant ops) config.constant ops
    fixed := fixed
    selectorRows := selectorRows }

/-- Project the certified compiler's data for the existing key-generation pipeline. -/
def CertifiedLayout.toDerivedLayout {ops : Operations F}
    {permutationColumns : List Halo2.Layout.ColRef} {config : Config} {planner : Planner}
    (_ : CertifiedLayout ops permutationColumns config planner) : DerivedLayout :=
  derivedLayout ops permutationColumns config planner

end Midnight.Chips.Layout
