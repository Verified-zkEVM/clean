import Clean.Ironwood.Action.SelectorPacking.Basic

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_0 :
    selectorActivationRows actionReducedSelectorActivations
      0 = expandSelectorRowRuns (actionSelectorRowRuns 0) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_1 :
    selectorActivationRows actionReducedSelectorActivations
      1 = expandSelectorRowRuns (actionSelectorRowRuns 1) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_4 :
    selectorActivationRows actionReducedSelectorActivations
      4 = expandSelectorRowRuns (actionSelectorRowRuns 4) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_5 :
    selectorActivationRows actionReducedSelectorActivations
      5 = expandSelectorRowRuns (actionSelectorRowRuns 5) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_6 :
    selectorActivationRows actionReducedSelectorActivations
      6 = expandSelectorRowRuns (actionSelectorRowRuns 6) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_7 :
    selectorActivationRows actionReducedSelectorActivations
      7 = expandSelectorRowRuns (actionSelectorRowRuns 7) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_8 :
    selectorActivationRows actionReducedSelectorActivations
      8 = expandSelectorRowRuns (actionSelectorRowRuns 8) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_9 :
    selectorActivationRows actionReducedSelectorActivations
      9 = expandSelectorRowRuns (actionSelectorRowRuns 9) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_10 :
    selectorActivationRows actionReducedSelectorActivations
      10 = expandSelectorRowRuns (actionSelectorRowRuns 10) := by
  action_selector_rows

end Zcash.Circuits.Action
