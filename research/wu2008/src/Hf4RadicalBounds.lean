import TerminalERadical

noncomputable section
namespace Hf4Target
theorem radical_bounds : (3872983346207/1000000000000 : ℝ) < TerminalE.radical ∧
    TerminalE.radical < 3872983346208/1000000000000 := by
  have hp := TerminalE.radical_pos
  have hs := TerminalE.radical_sq
  constructor <;> nlinarith only [hp, hs]

end Hf4Target
