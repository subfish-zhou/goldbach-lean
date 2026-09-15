import W12AcceptedCount

noncomputable section
open Real Wu2008DoubleSieve
open SharpLogRecurrence JointLogTotalComparison

namespace WuTarget.E08Debit

def splitLower (x : ℝ) : ℝ :=
  lowerLog ((x+1)/2) + lowerLog (2*x/(x+1))

def splitUpper (x : ℝ) : ℝ :=
  V ((x+1)/2) + V (2*x/(x+1))

theorem split_log {x : ℝ} (hx : 1 ≤ x) :
    log x = log ((x+1)/2) + log (2*x/(x+1)) := by
  have hp : 0 < x+1 := by linarith
  have h1 : 0 < (x+1)/2 := by positivity
  have h2 : 0 < 2*x/(x+1) := div_pos (by linarith) hp
  rw [← log_mul h1.ne' h2.ne']
  congr 1
  field_simp

theorem split_bounds {x : ℝ} (hx : 1 ≤ x) :
    splitLower x ≤ log x ∧ log x ≤ splitUpper x := by
  have h1 : (1 : ℝ) ≤ (x+1)/2 := by linarith
  have h2 : (1 : ℝ) ≤ 2*x/(x+1) :=
    (le_div_iff₀ (by linarith : 0 < x+1)).2 (by linarith)
  rw [split_log hx]
  exact ⟨add_le_add (log_lower h1) (log_lower h2),
    add_le_add (log_le_V h1) (log_le_V h2)⟩

#print SharpLogRecurrence.lowerLog
#print SharpLogRecurrence.upperLog
#print SignedTotalCorrelation.jTwo
#print SharpJBalance.ninthA
#print SharpJBalance.s
#print SeventhEighth.sigma
#print SeventhEighth.alpha
#print axioms split_bounds

end WuTarget.E08Debit
