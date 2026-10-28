module

public import Clean.Air.RowProgram
public import Clean.Circuit.Channel

@[expose] public section

/-!
# Component generation

How the prover builds the rows of a component: its `generation` field. The generator itself, and
the "chain reaction" that drives it, is described in `Clean.Air.WitnessGeneration`.

A component's generation is one of two modes:
- `demand`: the component starts without rows and gets a new row whenever its channel has an
  unanswered message. Examples are a VM, which gets one row per state, and an addition chip.
- `preallocated`: the component has a fixed number of rows from the start. Demand on its channel
  only changes the multiplicities of existing rows. Examples are a memory, which has one row per
  address, and a lookup table.

In both modes, the component answers demand on one channel, in one direction, its `trigger`.

Both modes describe the input of a row as a witness program producing the component's `Input`, with
a `Cell` for every input variable:
- `.fixed value`: a fixed column, whose value the verifier knows. It is computed from the row index
  alone, so only preallocated rows have fixed cells.
- `.witness value`: a value the prover computes, from the message a demand row answers, prover data
  and the hint. Witness IR expressions and circuit variables coerce to witness cells.
- `.multiplicity`: the multiplicity of the component's interaction on its channel.

A multiplicity cell makes a component answer repeated demand for a message by counting it in one
row: the generator finds the row whose interaction on the channel carries the message, and changes
the cell by the amount that cancels the demand. A row that pushes its message counts the pulls it
answers, and a row that pulls it counts the pushes.
Preallocated components must have exactly one multiplicity cell. For demand components, behavior
depends on whether you use a multiplicity cell in the input: if yes, the component gets one row per
distinct message, like an addition chip; if not, it gets one row per occurrence, like a VM, where
every step is its own row even if two steps happen to agree. For example, a memory row
emits `memoryChannel.emit multiplicity { address, value }`, so its input is
`{ address := .fixed i.toField, value := .witness ..., multiplicity := .multiplicity }`.

The component's witness programs compute the rest of the row from its input.

Several components may answer demand on the same channel. Each demanded message is then routed to
the one component that accepts it: a demand component accepts the messages its guard holds for, a
preallocated one those it has a row for. For example, the opcode tables of a VM share its state
channel, and each table's guard checks the opcode at the state's `pc`.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type}

/-- How generation fills one input cell of a component row. -/
inductive Cell (F : Type) where
  /-- A fixed column: a value the verifier knows, computed from the row index alone. -/
  | fixed (value : Witgen.FExpr F)
  /-- A value the prover computes. -/
  | witness (value : Witgen.FExpr F)
  /-- The multiplicity of the component's interaction on its channel, which generation counts. -/
  | multiplicity

namespace Cell

instance : Coe (Witgen.FExpr F) (Cell F) := ⟨.witness⟩
instance : Coe (Expression F) (Cell F) := ⟨fun e => .witness (.expr e)⟩
instance {n : ℕ} [OfNat F n] : OfNat (Cell F) n := ⟨.witness (OfNat.ofNat n)⟩
instance {M : TypeMap} [ProvableType M] : Coe (M (Expression F)) (M (Cell F)) where
  coe v := fromElements (toElements v |>.map fun e => .witness (.expr e))

/-- The value of the cell in a row whose multiplicity is `multiplicity`. -/
def eval [FiniteField F] (ctx : Witgen.Ctx F) (multiplicity : F) : Cell F → F
  | .fixed value | .witness value => value.eval ctx
  | .multiplicity => multiplicity

/-- An input value agrees with the cell evaluated in `ctx`, if the cell is fixed. -/
@[circuit_norm]
def FixedMatches [FiniteField F] (ctx : Witgen.Ctx F) : Cell F → F → Prop
  | .fixed value, input => input = value.eval ctx
  | .witness _, _ | .multiplicity, _ => True

instance [FiniteField F] (ctx : Witgen.Ctx F) : ∀ (cell : Cell F) (input : F),
    Decidable (FixedMatches ctx cell input)
  | .fixed value, input => inferInstanceAs (Decidable (input = value.eval ctx))
  | .witness _, _ | .multiplicity, _ => inferInstanceAs (Decidable True)

def isMultiplicity : Cell F → Bool
  | .multiplicity => true
  | _ => false

def isFixed : Cell F → Bool
  | .fixed _ => true
  | _ => false

end Cell

/-- The input cells a program computes, as a vector, and its `let`-steps. -/
def inputCells {Input : TypeMap} [ProvableType Input] (program : Witgen.M F (Input (Cell F))) :
    Vector (Cell F) (size Input) × List (Witgen.Step F) :=
  let (cells, steps) := program #[]
  (toElements cells, steps.toList)

/-- The context in which the cells of a program are evaluated: `env`, at row `row`. -/
@[circuit_norm]
def inputContext [FiniteField F] (steps : List (Witgen.Step F)) (env : ProverEnvironment F)
    (row : ℕ) : Witgen.Ctx F :=
  { env, locals := Witgen.evalSteps env steps #[] row, idx := row }

/-- Evaluate an input program in `env` at row `row`, with multiplicity `multiplicity`. -/
def evalInput [FiniteField F] {Input : TypeMap} [ProvableType Input]
    (program : Witgen.M F (Input (Cell F))) (env : ProverEnvironment F) (row : ℕ)
    (multiplicity : F) : Array F :=
  let (cells, steps) := inputCells program
  (cells.map (Cell.eval (inputContext steps env row) multiplicity)).toArray

/-- The environment of a row program: no row cells and no prover data, only the hint. -/
@[circuit_norm]
def rowEnvironment [FiniteField F] (hint : ProverHint F) : ProverEnvironment F :=
  { get _ := 0, data _ _ := #[], hint }

/-- Rows created by channel demand. -/
structure DemandMode (F : Type) [FiniteField F] (Input : TypeMap) [ProvableType Input] where
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
  /-- The input of a new row, built from the message it answers. A multiplicity cell starts at the
  value that cancels the demand. -/
  input : Var Message F → Witgen.M F (Input (Cell F))
  /-- The input of the rows appended after balancing, to make the table's height a power of two.
  Padding rows are completed by the component's witness programs like any other row; if they
  interact, the generator balances again. -/
  padding : Input F := 0

/-- A fixed number of rows, which answer demand on the channel by counting it in their multiplicity
cell. The fixed cells of all rows are the component's fixed columns. -/
structure PreallocatedMode (F : Type) (Input : TypeMap) [ProvableType Input] where
  {Message : TypeMap} [provableMessage : ProvableType Message]
  /-- The channel on which the rows answer demand. -/
  channel : Channel F Message
  /-- Which unanswered messages the rows answer: `.pull` means messages pulled more often than
  pushed, like the reads of a lookup table, which a row pushing its message counts; `.push` means
  the opposite. -/
  trigger : Direction
  /-- The number of rows, a power of two. -/
  height : UInt64
  /-- The input of row `i`. Its `let`-steps and fixed cells are computed from `i` alone; its witness
  cells may also read the hint. Its multiplicity cell starts at 0. -/
  input (i : Witgen.U64Expr F) : Witgen.M F (Input (Cell F))

variable [FiniteField F]

instance {Input : TypeMap} [ProvableType Input] (mode : DemandMode F Input) :
    ProvableType mode.Message :=
  mode.provableMessage

instance {Input : TypeMap} [ProvableType Input] (mode : PreallocatedMode F Input) :
    ProvableType mode.Message :=
  mode.provableMessage

/-- The guard as a condition on the cells of the message. -/
def DemandMode.guardCondition {Input : TypeMap} [ProvableType Input] (mode : DemandMode F Input) :
    Witgen.BExpr F :=
  mode.guard (varFromOffset mode.Message 0)

/-- How the generator builds the rows of a component with input `Input`. -/
inductive Generation (F : Type) [FiniteField F] (Input : TypeMap) [ProvableType Input] where
  | demand (mode : DemandMode F Input)
  | preallocated (mode : PreallocatedMode F Input)

namespace Generation
variable {Input : TypeMap} [ProvableType Input]

/-- The name of the channel on which the component answers demand. -/
def channelName : Generation F Input → String
  | .demand mode => mode.channel.name
  | .preallocated mode => mode.channel.name

/-- The input cells of a row, with the program's `let`-steps: those of a demand row, whose message
is in the first cells of the environment, or those of a preallocated row, whose index is `.idx`. -/
def cells : Generation F Input → Vector (Cell F) (size Input) × List (Witgen.Step F)
  | .demand mode => inputCells (mode.input (varFromOffset mode.Message 0))
  | .preallocated mode => inputCells (mode.input .idx)

end Generation

/-! ### Fixed cells -/

namespace PreallocatedMode
variable {Input : TypeMap} [ProvableType Input]

/-- The input agrees with the fixed cells of row `i`. -/
@[circuit_norm]
def FixedAt (mode : PreallocatedMode F Input) (i : UInt64) (input : Input F) : Prop :=
  let (cells, steps) := mode.input .idx #[]
  List.Forall₂ (Cell.FixedMatches (inputContext steps.toList (rowEnvironment (.empty F)) i.toNat))
    (toElements cells).toList (toElements input).toList

instance (mode : PreallocatedMode F Input) (i : UInt64) (input : Input F) :
    Decidable (mode.FixedAt i input) :=
  inferInstanceAs (Decidable (List.Forall₂ _ _ _))

end PreallocatedMode

/-- The fixed-column fact about the input of row `i`: in a preallocated component, the row lies
within the height, and the input agrees with the row's fixed cells. -/
@[circuit_norm]
def Generation.FixedInputAt {Input : TypeMap} [ProvableType Input] :
    Generation F Input → UInt64 → Input F → Prop
  | .demand _, _, _ => True
  | .preallocated mode, i, input => i < mode.height ∧ mode.FixedAt i input

/-! ### Padding -/

def nextPowerOfTwoAux (target : ℕ) : ℕ → ℕ → ℕ
  | 0, power => power
  | fuel + 1, power =>
      if target ≤ power then power else nextPowerOfTwoAux target fuel (power * 2)

def nextPowerOfTwo (value : ℕ) : ℕ :=
  nextPowerOfTwoAux (max value 1) value 1

end Air.Flat.WitnessGeneration
