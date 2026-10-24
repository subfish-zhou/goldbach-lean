import WSrcFourEnclosureLogs
import FirstIntegralEnvelope

noncomputable section
namespace WuPaper.ClassicalLogSplit
open Real

def lower : ℕ → ℝ → ℝ
  | 0, t => WuSource.SrcFourEnclosure.logLo t
  | n+1, t => lower n ((1+t)/2)+lower n (2*t/(1+t))

def upper : ℕ → ℝ → ℝ
  | 0, t => WuSource.SrcFourEnclosure.logHi t
  | n+1, t => upper n ((1+t)/2)+upper n (2*t/(1+t))

/-- Exact multiplicative splitting keeps the rational logarithm arguments near one. -/
theorem bounds (n : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ lower n t ∧ lower n t ≤ log t ∧ log t ≤ upper n t := by
  induction n generalizing t with
  | zero => exact WuSource.SrcFourEnclosure.log_bounds ht
  | succ n ih =>
    obtain ⟨ha,hb⟩ := FirstIntegralRecovery.split_arguments ht
    obtain ⟨ha0,haL,haU⟩ := ih ha
    obtain ⟨hb0,hbL,hbU⟩ := ih hb
    rw [FirstIntegralRecovery.split_log_identity ht]
    exact ⟨add_nonneg ha0 hb0,add_le_add haL hbL,add_le_add haU hbU⟩

end WuPaper.ClassicalLogSplit
#print axioms WuPaper.ClassicalLogSplit.bounds
