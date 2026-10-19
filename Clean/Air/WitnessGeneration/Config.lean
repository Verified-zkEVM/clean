module

public import Clean.Air.FlatEnsemble

@[expose] public section

/-!
# Witness generation config

What the ensemble author writes to generate witnesses: for every component, how its rows come into
existence. The generator itself, and the "chain reaction" that drives it, is described in
`Clean.Air.WitnessGeneration`. A generation `Generation c` is indexed by its component `c`, and a
`Config` lists every ensemble component with its generation.

A component's generation is one of two modes:
- `demand`: the component starts without rows and gets a new row whenever its channel has an
  unanswered message. Examples are a VM, which gets one row per state, and an addition chip.
- `preallocated`: the component's rows exist from the start, one per row of its fixed columns.
  Demand only increments the multiplicities of existing rows. Examples are a memory, which has one
  row per address, and a lookup table.

Rows that answer repeated demand for the same message, in a `byMessage` demand component or a
preallocated one, do so through a *counter*: an input variable that is the multiplicity of one of
the row's interactions. The config names the variable, and the generator finds the interaction.
For example, a memory row emits `memoryChannel.emit multiplicity { address, value }`, so its config
names the counter `fun row => row.multiplicity`. The generator finds the row whose counted
interaction carries the demanded message and increments its counter. Since a counter only adds
pushes, it answers messages pulled more often than pushed.

Fixed columns are never generated: they are part of the component, and the generator copies them
into the first cells of every row. So configs only describe the cells after the fixed columns. That
is why only components with fixed columns can be preallocated, and those components must be.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type}

/-- Whether a channel message was pushed or pulled. -/
inductive Direction where
  | pull
  | push
deriving Repr, DecidableEq, BEq

def Direction.name : Direction → String
  | .pull => "pull"
  | .push => "push"

/-- How a demand-generated component `c` answers the same message demanded several times. -/
inductive Aggregation [FiniteField F] (c : Component F) where
  /-- One row per occurrence. Right for a VM, where every step is its own row even if two steps
  happen to agree. -/
  | perOccurrence
  /-- One row per distinct message, whose `counter` counts the occurrences, named by its input
  variable like `fun row => row.multiplicity`. Right for chips whose rows only depend on their
  message, like an addition chip. Only answers pull surplus, see counters in the module doc. -/
  | byMessage (counter : Var c.Input F → Expression F)

/-- One input cell of a demand-generated row. -/
inductive InputCell (F : Type) where
  /-- Element `index` of the demanded message. -/
  | message (index : ℕ)
  /-- A constant, like an enabled flag. -/
  | const (value : F)

def InputCell.eval (message : Array F) [Zero F] : InputCell F → F
  | .message index => message[index]?.getD 0
  | .const value => value

/-- The rows appended to a demand-generated table after balancing, to make its height a power of
two. -/
structure Padding (F : Type) where
  /-- The input of every padding row. Padding rows are completed by the component's witness programs
  like any other row; if they interact, the generator balances again. -/
  input : Array F
  /-- The table has at least this many rows. -/
  minimumRows : UInt64 := 1

/-- Rows of component `c` created by channel demand. -/
structure DemandMode [FiniteField F] (c : Component F) where
  /-- The channel whose unanswered messages create rows of this component. -/
  channel : RawChannel F
  /-- Which unanswered messages create rows: `.push` means messages pushed more often than pulled,
  so the new row pulls them; `.pull` means the opposite. -/
  surplus : Direction
  /-- Whether repeated demand for one message creates repeated rows. -/
  aggregation : Aggregation c
  /-- The input of a new row, cell by cell, built from the message it answers. With `byMessage`, the
  cells skip the counter, which starts at the demanded count. The component's witness programs
  compute the rest of the row. -/
  input : List (InputCell F)
  padding : Padding F

/-- One row of component `c` per fixed row, with the given counters.

The input of row `i` consists of:
- the fixed columns of row `i`, which come first,
- the counters, wherever the circuit puts them, which start at 0,
- the values of `row i` from `RowProgram`, which fill the remaining cells in order.

For example, a memory row emits `memoryChannel.emit multiplicity { address, value }`: its fixed
column is `address`, its row program computes `value`, and `multiplicity` is its counter. -/
structure PreallocatedMode [FiniteField F] (c : Component F) extends Witgen.RowProgram F .prover
    where
  /-- The counters, named by their input variables like `fun row => row.multiplicity`. The
  component answers demand on the channels of the counted interactions. -/
  counters : List (Var c.Input F → Expression F)

/-- How the generator builds the rows of component `c`. -/
inductive Generation [FiniteField F] (c : Component F) where
  | demand (mode : DemandMode c)
  | preallocated (mode : PreallocatedMode c)

/-- Generation for a whole ensemble. -/
structure Config [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]
    (ens : FormalEnsemble F PublicIO) where
  /-- Every ensemble component with its generation, in ensemble order. -/
  generations : List ((c : Component F) × Generation c)
  /-- The config lists exactly the ensemble's components. -/
  same_components : generations.map (·.1) = ens.ensemble.tables := by rfl
  /-- Bounds the number of generation steps. -/
  fuel : ℕ

/-! ### Padding -/

def nextPowerOfTwoAux (target : ℕ) : ℕ → ℕ → ℕ
  | 0, power => power
  | fuel + 1, power =>
      if target ≤ power then power else nextPowerOfTwoAux target fuel (power * 2)

def nextPowerOfTwo (value : ℕ) : ℕ :=
  nextPowerOfTwoAux (max value 1) value 1

/-- The padded height of a table with `rowCount` rows. -/
def Padding.targetHeight (padding : Padding F) (rowCount : ℕ) : ℕ :=
  nextPowerOfTwo (max rowCount padding.minimumRows.toNat)

end Air.Flat.WitnessGeneration
