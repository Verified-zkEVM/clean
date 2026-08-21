import Clean.Ironwood.Action.SelectorPacking.Rows0

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_11 :
    selectorActivationRows actionReducedSelectorActivations
      11 = expandSelectorRowRuns (actionSelectorRowRuns 11) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_12 :
    selectorActivationRows actionReducedSelectorActivations
      12 = expandSelectorRowRuns (actionSelectorRowRuns 12) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_13 :
    selectorActivationRows actionReducedSelectorActivations
      13 = expandSelectorRowRuns (actionSelectorRowRuns 13) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_14 :
    selectorActivationRows actionReducedSelectorActivations
      14 = expandSelectorRowRuns (actionSelectorRowRuns 14) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_15 :
    selectorActivationRows actionReducedSelectorActivations
      15 = expandSelectorRowRuns (actionSelectorRowRuns 15) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_16 :
    selectorActivationRows actionReducedSelectorActivations
      16 = expandSelectorRowRuns (actionSelectorRowRuns 16) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_17 :
    selectorActivationRows actionReducedSelectorActivations
      17 = expandSelectorRowRuns (actionSelectorRowRuns 17) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_18 :
    selectorActivationRows actionReducedSelectorActivations
      18 = expandSelectorRowRuns (actionSelectorRowRuns 18) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_19 :
    selectorActivationRows actionReducedSelectorActivations
      19 = expandSelectorRowRuns (actionSelectorRowRuns 19) := by
  action_selector_rows

end Zcash.Circuits.Action
