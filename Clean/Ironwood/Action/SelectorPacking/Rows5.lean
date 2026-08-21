import Clean.Ironwood.Action.SelectorPacking.Rows4

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_49 :
    selectorActivationRows actionReducedSelectorActivations
      49 = expandSelectorRowRuns (actionSelectorRowRuns 49) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_50 :
    selectorActivationRows actionReducedSelectorActivations
      50 = expandSelectorRowRuns (actionSelectorRowRuns 50) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_51 :
    selectorActivationRows actionReducedSelectorActivations
      51 = expandSelectorRowRuns (actionSelectorRowRuns 51) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_52 :
    selectorActivationRows actionReducedSelectorActivations
      52 = expandSelectorRowRuns (actionSelectorRowRuns 52) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_53 :
    selectorActivationRows actionReducedSelectorActivations
      53 = expandSelectorRowRuns (actionSelectorRowRuns 53) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_54 :
    selectorActivationRows actionReducedSelectorActivations
      54 = expandSelectorRowRuns (actionSelectorRowRuns 54) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_55 :
    selectorActivationRows actionReducedSelectorActivations
      55 = expandSelectorRowRuns (actionSelectorRowRuns 55) := by
  action_selector_rows

end Zcash.Circuits.Action
