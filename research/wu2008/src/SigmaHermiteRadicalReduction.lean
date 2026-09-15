import SigmaHermiteBlocks

noncomputable section
namespace SigmaHermiteActualFTC

/-- Exact reduction at the original algebraic radical, without root approximation. -/
theorem radical_power_reduce (n : ℕ) :
    TerminalE.radical^(n+2) = 15*TerminalE.radical^n := by
  rw [pow_add, TerminalE.radical_sq]
  ring

end SigmaHermiteActualFTC
