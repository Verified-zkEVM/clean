import Clean.Ironwood.Action.SelectorPacking.Rows3

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_40 :
    selectorActivationRows actionReducedSelectorActivations
      40 = expandSelectorRowRuns (actionSelectorRowRuns 40) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_41 :
    selectorActivationRows actionReducedSelectorActivations
      41 = expandSelectorRowRuns (actionSelectorRowRuns 41) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_42 :
    selectorActivationRows actionReducedSelectorActivations
      42 = expandSelectorRowRuns (actionSelectorRowRuns 42) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_43 :
    selectorActivationRows actionReducedSelectorActivations
      43 = expandSelectorRowRuns (actionSelectorRowRuns 43) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_44 :
    selectorActivationRows actionReducedSelectorActivations
      44 = expandSelectorRowRuns (actionSelectorRowRuns 44) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_45 :
    selectorActivationRows actionReducedSelectorActivations
      45 = expandSelectorRowRuns (actionSelectorRowRuns 45) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_46 :
    selectorActivationRows actionReducedSelectorActivations
      46 = expandSelectorRowRuns (actionSelectorRowRuns 46) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_47 :
    selectorActivationRows actionReducedSelectorActivations
      47 = expandSelectorRowRuns (actionSelectorRowRuns 47) := by
  action_selector_rows

set_option maxRecDepth 1000000 in
@[action_selector_rows_norm]
theorem actionSelectorActivationRows_48 :
    selectorActivationRows actionReducedSelectorActivations
      48 = expandSelectorRowRuns (actionSelectorRowRuns 48) := by
  action_selector_rows

end Zcash.Circuits.Action
