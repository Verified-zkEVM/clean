import Clean.Halo2.WitnessSupport

namespace Halo2.Tests.TestWitnessSupport

variable {F : Type} [FiniteField F]

/-! `supported%` finds the read set by unification, for Clean's own program shapes. -/

-- A constant native program reads nothing.
example : (supported% (.native fun _ => #v[(3 : F)]) : SupportedProgram F).reads = [] := rfl

-- A native wrapper of a cell read reads that cell.
example (cell : AssignedCell F) :
    (supported% (.native fun env => #v[readCell env cell]) : SupportedProgram F).reads =
      [cell] := rfl

-- A function parameter, scalar and Boolean.
example (cell : AssignedCell F) :
    (supported% (fun env => readCell env cell) : SupportedFunction F F).reads = [cell] := rfl

example : (supported% (fun _ => true) : SupportedFunction F Bool).reads = [] := rfl

/-! The certificate carried by a supported parameter is a rule, so a gadget's program built
from the parameter is supported too. -/

example (p : SupportedProgram F) :
    WitnessFunctionSupport p.reads (programFunction p.program) := by
  solve_witness_support

example (f : SupportedFunction F Bool) :
    (supported% (.native fun env => #v[if f.compute env then (1 : F) else 0]) :
      SupportedProgram F).reads = f.reads := rfl

example (f : SupportedFunction F F) :
    (supported% (.native fun env => #v[f.compute env]) : SupportedProgram F).reads =
      f.reads := rfl

-- A function of the assignment is certified through its lift.
example : (supported% (fun _ => (0 : F)) : SupportedEnvironmentFunction F F).reads = [] := rfl

example (f : SupportedEnvironmentFunction F F) :
    (supported% (.native fun env => #v[f.compute env.toEnvironment]) :
      SupportedProgram F).reads = f.reads := rfl

end Halo2.Tests.TestWitnessSupport
