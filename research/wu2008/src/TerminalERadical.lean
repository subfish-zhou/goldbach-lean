import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section
namespace TerminalE
open Real
def radical : ℝ := sqrt 15
theorem radical_pos : 0 < radical := by unfold radical; positivity
theorem radical_sq : radical^2=15 := by unfold radical; exact sq_sqrt (by norm_num)
theorem radical_lt_four : radical<4 := by nlinarith only [radical_pos,radical_sq]

end TerminalE
