import Clean.Gadgets.SHA256.LowerSigma0
import Clean.Gadgets.SHA256.LowerSigma1
import Clean.Gadgets.SHA256.Add32
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Gadgets.SHA256

/-!
# SHA-256 Message Schedule

Expands a 16-word block into a 64-word message schedule.

For i in 16..63:
  w[i] = σ₁(w[i−2]) + w[i−7] + σ₀(w[i−15]) + w[i−16]  (mod 2^32)

Per step, `scheduleStep` creates:
  - lowerSigma1: 2 × xor32 = 2 × 32 = 64 witness variables
  - lowerSigma0: 2 × xor32 = 64 witness variables
  - 3 × add32    = 3 × 33  = 99 witness variables
  Total: 64 + 64 + 99 = 227 variables per step.
-/

private abbrev Schedule := Vector (Var (fields 32) (F p)) 64

/-- One step of the message schedule: compute w[j] for j = i.val + 16. -/
private def scheduleStep (w : Schedule (p := p)) (i : Fin 48) :
    Circuit (F p) (Schedule (p := p)) := do
  let j := i.val + 16
  let s1   ← lowerSigma1 (w.get ⟨j - 2,  by omega⟩)
  let s0   ← lowerSigma0 (w.get ⟨j - 15, by omega⟩)
  let sum0 ← add32 s1           (w.get ⟨j - 7,  by omega⟩)
  let sum1 ← add32 sum0 s0
  let wj   ← add32 sum1         (w.get ⟨j - 16, by omega⟩)
  return w.set (⟨j, by omega⟩ : Fin 64) wj

private instance :
    Circuit.ConstantLength (fun (x : Schedule (p := p) × Fin 48) => scheduleStep x.1 x.2) where
  localLength := 227
  localLength_eq _ _ := by sorry

/-- Expand a 16-word block into a 64-word message schedule.
    Each word is a `Var (fields 32) (F p)` (32-bit boolean vector, LSB first). -/
@[irreducible] def messageSchedule (block : Vector (Var (fields 32) (F p)) 16) :
    Circuit (F p) (Schedule (p := p)) := do
  -- Initialise: first 16 words from block, next 48 as zero placeholders.
  let zero32 : Var (fields 32) (F p) := Vector.replicate 32 (0 : Expression (F p))
  let init : Schedule (p := p) := block.append (Vector.replicate 48 zero32)
  -- Expand indices 16..63 one at a time.
  -- Pass ConstantLength explicitly because the default tactic times out on this complex body.
  Circuit.foldlRange 48 init (fun w i => scheduleStep w i) ⟨227, fun _ _ => by sorry⟩

namespace MessageSchedule

def main (block : Var SHA256Block (F p)) : Circuit (F p) (Var SHA256Schedule (F p)) :=
  messageSchedule block

instance elaborated : ElaboratedCircuit (F p) SHA256Block SHA256Schedule where
  main := main
  localLength _ := 48 * 227
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry
  channelsLawful := by sorry

def Assumptions (block : SHA256Block (F p)) : Prop :=
  ∀ i : Fin 16, Normalized block[i]

def Spec (block : SHA256Block (F p)) (sched : SHA256Schedule (F p)) : Prop :=
  let block_val : Vector ℕ 16 := block.map valueBits
  let expected := Specs.SHA256.messageSchedule block_val
  ∀ i : Fin 64, valueBits sched[i] = expected[i] ∧ Normalized sched[i]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by sorry
theorem completeness : Completeness (F p) elaborated Assumptions := by sorry

def circuit : FormalCircuit (F p) SHA256Block SHA256Schedule where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end MessageSchedule
end Gadgets.SHA256
end
