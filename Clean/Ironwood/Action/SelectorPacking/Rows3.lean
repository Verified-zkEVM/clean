import Clean.Ironwood.Action.SelectorPacking.Rows2

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_31 :
    selectorActivationRows actionReducedSelectorActivations
      31 = expandSelectorRowRuns (actionSelectorRowRuns 31) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_32 :
    selectorActivationRows actionReducedSelectorActivations
      32 = expandSelectorRowRuns (actionSelectorRowRuns 32) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_33 :
    selectorActivationRows actionReducedSelectorActivations
      33 = expandSelectorRowRuns (actionSelectorRowRuns 33) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_34 :
    selectorActivationRows actionReducedSelectorActivations
      34 = expandSelectorRowRuns (actionSelectorRowRuns 34) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_35 :
    selectorActivationRows actionReducedSelectorActivations
      35 = expandSelectorRowRuns (actionSelectorRowRuns 35) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_36 :
    selectorActivationRows actionReducedSelectorActivations
      36 = expandSelectorRowRuns (actionSelectorRowRuns 36) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_37 :
    selectorActivationRows actionReducedSelectorActivations
      37 = expandSelectorRowRuns (actionSelectorRowRuns 37) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_38 :
    selectorActivationRows actionReducedSelectorActivations
      38 = expandSelectorRowRuns (actionSelectorRowRuns 38) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_39 :
    selectorActivationRows actionReducedSelectorActivations
      39 = expandSelectorRowRuns (actionSelectorRowRuns 39) := by
  action_selector_rows

end Zcash.Circuits.Action
