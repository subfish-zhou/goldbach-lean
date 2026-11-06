import Wu08TerminalAlignment

noncomputable section
open Real Wu2008DoubleSieve
open SharpLogRecurrence BaseRecurrenceLower
namespace FirstPublicationAudit

/-- The published number is a target, not an assumed estimate. -/
def publicationTarget : ℝ := 14900897/1000000

/-- The already proved affine/quadratic certificate, in collected endpoint form.
This is a lower certificate for F1, not a second recurrence payment. -/
def inheritedEndpoint : ℝ := 8*(log 3 + (4^2-3^2)/18-(2/3)*(4-3)+
    2*log (4/3)+(56/243)*(5-4)+(34832/30375-4*(56/243))*log (5/4)+
    (2776/10125)*(1127/200-5)+(340/243-5*(2776/10125))*log (1127/1000))


/-- Exact rational ceiling on the inherited certificate ONLY. It is not an upper
bound on the true F1. Its failure leaves the direct integral task open. -/
def inheritedCeiling : ℝ :=
  346606556110596054975424/23347250566838165953125

theorem inheritedEndpoint_le_ceiling : inheritedEndpoint ≤ inheritedCeiling := by
  have h3 := log_three_bounds.2
  have h43 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 4/3)
  have h54 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 5/4)
  have hlast := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 1127/1000)
  norm_num [JointLogTotalComparison.V,upperLog,lowerLog] at h43 h54 hlast
  unfold inheritedEndpoint inheritedCeiling
  linarith only [h3,h43,h54,hlast]




end FirstPublicationAudit
