import WR2ExactRationalLogData
import WSrcFourEnclosureLogs

/-! Exact rational evaluation of the existing twelve-term logarithm bounds.
The cast identities preserve the real formulas, including their remainders.
Finite certificates use kernel reduction of rational inequalities. -/

namespace WuPaper.ExactRational
open Finset

@[simp] theorem cast_logLo (t : ℚ) :
    (logLo t : ℝ) = WuSource.SrcFourEnclosure.logLo (t : ℝ) := by
  simp [logLo, WuSource.SrcFourEnclosure.logLo]

@[simp] theorem cast_logHi (t : ℚ) :
    (logHi t : ℝ) = WuSource.SrcFourEnclosure.logHi (t : ℝ) := by
  simp [logHi, WuSource.SrcFourEnclosure.logHi]

end WuPaper.ExactRational
