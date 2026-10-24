import Wu04FactorEnvelopes

/-! A fixed four-factor rational logarithm bound for Xi2 cell certificates. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Wu04FactorEnvelopes Wu2008DoubleSieve

def cellLogLower (x : ℝ) : ℝ := lower (leftFactor x) + lower (rightFactor x)

theorem cellLogLower_le_log {x : ℝ} (hx : 1 ≤ x) : cellLogLower x ≤ log x := by
  rw [exact_log hx]
  exact add_le_add (lower_le_log (factors hx).1) (lower_le_log (factors hx).2.1)

theorem cellLogLower_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ cellLogLower x := by
  have hlower {y : ℝ} (hy : 1 ≤ y) : 0 ≤ lower y := by
    have hl := (factors hy).1
    have hr := (factors hy).2.1
    unfold lower SharpLogRecurrence.lowerLog
    positivity
  exact add_nonneg (hlower (factors hx).1) (hlower (factors hx).2.1)

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.cellLogLower_le_log
#print axioms WuPaper.R2Xi.cellLogLower_nonneg
