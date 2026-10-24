module

public import Clean.Air.RowProgram
public import Clean.Circuit.Channel

@[expose] public section

/-!
# Component generation

How the prover builds the rows of a component: its `generation` field. The generator itself, and
the "chain reaction" that drives it, is described in `Clean.Air.WitnessGeneration`.

A component's generation is one of three modes:
- `demand`: the component starts without rows and gets a new row whenever its channel has an
  unanswered message. Examples are a VM, which gets one row per state, and an addition chip.
- `preallocated`: the component's rows exist from the start, one per row of its fixed columns.
  Demand only increments the multiplicities of existing rows. Examples are a memory, which has one
  row per address, and a lookup table.
- `segments`: the component's rows exist from the start, one per row of its fixed columns, and are
  computed by a segment program, in segments of consecutive rows where each row continues from the
  previous one. They have no counters, so they never answer demand. An example is Plonky3's Keccak
  AIR, whose 24 rows per permutation each compute a round from the previous round's output.

Rows that answer repeated demand for the same message, in a `byMessage` demand component or a
preallocated one, do so through a *counter*: an input variable that is the multiplicity of one of
the row's interactions. The generation names the variable, and the generator finds the interaction.
For example, a memory row emits `memoryChannel.emit multiplicity { address, value }`, so its
generation names the counter `fun row => row.multiplicity`. The generator finds the row whose
counted interaction carries the demanded message and increments its counter. Since a counter only
adds pushes, it answers messages pulled more often than pushed.

Fixed columns are never generated: they are part of the component, and the generator copies them
into the first cells of every row. So generations only describe the cells after the fixed columns.
A component is preallocated or segment-generated exactly when it has fixed columns, which the
component requires. The
fixed columns may have no values, `Row := unit`, and only fix the height.

Several components may answer demand on the same channel. Each demanded message is then routed to
the one component that accepts it: a demand component accepts the messages its guard holds for, a
preallocated one those it has a row for. For example, the opcode tables of a VM share its state
channel, and each table's guard checks the opcode at the state's `pc`.
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

/-- How a demand-generated component with input `Input` answers the same message demanded several
times. -/
inductive Aggregation (F : Type) (Input : TypeMap) [ProvableType Input] where
  /-- One row per occurrence. Right for a VM, where every step is its own row even if two steps
  happen to agree. -/
  | perOccurrence
  /-- One row per distinct message, whose `counter` counts the occurrences, named by its input
  variable like `fun row => row.multiplicity`. Right for chips whose rows only depend on their
  message, like an addition chip. Only answers unmatched pulls, see counters in the module doc. -/
  | byMessage (counter : Var Input F → Expression F)

/-- One input cell of a demand-generated row. -/
inductive InputCell (F : Type) where
  /-- Element `index` of the demanded message. -/
  | message (index : ℕ)
  /-- A constant, like an enabled flag. -/
  | const (value : F)

def InputCell.eval (message : Array F) [Zero F] : InputCell F → F
  | .message index => message[index]?.getD 0
  | .const value => value

/-- Rows created by channel demand. -/
structure DemandMode (F : Type) (Input : TypeMap) [ProvableType Input] where
  {Message : TypeMap} [provableMessage : ProvableType Message]
  /-- The channel whose unanswered messages create rows of this component. -/
  channel : Channel F Message
  /-- Which unanswered messages create rows: `.push` means messages pushed more often than pulled,
  so the new row pulls them; `.pull` means the opposite. -/
  trigger : Direction
  /-- Which of these messages the component answers, by default all of them. Components sharing a
  channel, like the opcode tables of a VM, are told apart by guards. A guard is a witness program
  over the message, so it can read prover data and hints, like the opcode at the message's `pc`. -/
  guard : Var Message F → Witgen.BExpr F := fun _ => .true
  /-- Whether repeated demand for one message creates repeated rows. -/
  aggregation : Aggregation F Input
  /-- The input of a new row, cell by cell, built from the message it answers. With `byMessage`, the
  cells skip the counter, which starts at the demanded count. The component's witness programs
  compute the rest of the row. -/
  input : List (InputCell F)
  /-- The input of the rows appended after balancing, to make the table's height a power of two.
  Padding rows are completed by the component's witness programs like any other row; if they
  interact, the generator balances again. -/
  padding : Array F

/-- One row per fixed row, with the given counters.

The input of row `i` consists of:
- the fixed columns of row `i`, which come first,
- the counters, wherever the circuit puts them, which start at 0,
- the values of `row i` from `RowProgram`, which fill the remaining cells in order.

For example, a memory row emits `memoryChannel.emit multiplicity { address, value }`: its fixed
column is `address`, its row program computes `value`, and `multiplicity` is its counter. -/
structure PreallocatedMode (F : Type) (Input : TypeMap) [ProvableType Input]
    extends Witgen.RowProgram F .prover where
  /-- The counters, named by their input variables like `fun row => row.multiplicity`. The
  component answers demand on the channels of the counted interactions. -/
  counters : List (Var Input F → Expression F)

instance {Input : TypeMap} [ProvableType Input] (mode : DemandMode F Input) :
    ProvableType mode.Message :=
  mode.provableMessage

/-- The guard as a condition on the cells of the message. -/
def DemandMode.guardCondition {Input : TypeMap} [ProvableType Input] (mode : DemandMode F Input) :
    Witgen.BExpr F :=
  mode.guard (varFromOffset mode.Message 0)

/-- How the generator builds the rows of a component with input `Input`. -/
inductive Generation (F : Type) (Input : TypeMap) [ProvableType Input] where
  | demand (mode : DemandMode F Input)
  | preallocated (mode : PreallocatedMode F Input)
  /-- Rows computed by a segment program, whose values fill the cells after the fixed columns. -/
  | segments (program : Witgen.SegmentProgram F)

/-- Whether the rows exist from the start, one per row of the fixed columns. -/
def Generation.isPreallocated {Input : TypeMap} [ProvableType Input] :
    Generation F Input → Bool
  | .demand _ => false
  | .preallocated _ | .segments _ => true

/-! ### Padding -/

def nextPowerOfTwoAux (target : ℕ) : ℕ → ℕ → ℕ
  | 0, power => power
  | fuel + 1, power =>
      if target ≤ power then power else nextPowerOfTwoAux target fuel (power * 2)

def nextPowerOfTwo (value : ℕ) : ℕ :=
  nextPowerOfTwoAux (max value 1) value 1

end Air.Flat.WitnessGeneration
