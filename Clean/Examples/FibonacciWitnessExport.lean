import Clean.Examples.FibonacciWithChannels
import Clean.Air.WitnessExport
import Clean.Utils.Primes

/-! Build-time export consumed by witness code generators. -/

def main : IO Unit := do
  IO.println (← Air.Flat.WitnessGeneration.Export.jsonString
    (fibonacciEnsemble (p := pBabybear)).ensemble
    (FibonacciWitness.config (p := pBabybear)))
