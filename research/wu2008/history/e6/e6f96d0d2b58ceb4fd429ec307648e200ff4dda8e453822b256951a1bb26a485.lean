import W09ScalarTactics

namespace WuTarget.W09

example : True := by
  have h : Wu04RemainingStrongPublication.slack (Fin.succ (Fin.succ (0 : Fin 1))) =
      Wu04RemainingStrongPublication.slack 2 := rfl
  conv_lhs at h => tactic => w09_remaining_scalar
  trace_state
  trivial

example : True := by
  have h : Wu04FirstPublication.slack (Fin.succ (Fin.succ (0 : Fin 2))) =
      Wu04FirstPublication.slack 2 := rfl
  conv_lhs at h => tactic => w09_first_scalar
  trace_state
  trivial

example : True := by
  have h : Wu04FirstPublication.slack (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))) =
      Wu04FirstPublication.slack 3 := rfl
  conv_lhs at h => tactic => w09_first_scalar
  trace_state
  trivial

end WuTarget.W09
