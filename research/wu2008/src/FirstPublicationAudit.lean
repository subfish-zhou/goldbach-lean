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

/-- Reuse the actual ancestor theorem and first-slot identity; no ancestor rebuild. -/
theorem inheritedEndpoint_le_first : inheritedEndpoint ≤ Wu08TerminalAlignment.firstMain := by
  have h := alpha_real_lower
  rw [Q_difference (by norm_num) (by norm_num),
    P_difference 4 (34832/30375) (56/243) (by norm_num) (by norm_num),
    P_difference 5 (340/243) (2776/10125) (by norm_num) (by norm_num)] at h
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 8)
  rw [Wu08TerminalAlignment.first_exact] at hm
  norm_num at hm
  unfold inheritedEndpoint
  linarith only [hm]

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

/-- A proved obstruction for this inherited certificate, not for the publication. -/
theorem inherited_certificate_insufficient : inheritedEndpoint < publicationTarget := by
  have h : inheritedCeiling < publicationTarget := by
    norm_num [inheritedCeiling,publicationTarget]
  exact inheritedEndpoint_le_ceiling.trans_lt h

theorem inherited_ceiling_deficit : publicationTarget-inheritedCeiling =
    82458868419268579903901/1494224036277642621000000 := by
  norm_num [publicationTarget,inheritedCeiling]

/-- The exact still-unproved analytic obligation. C and E occur ONCE; this iff is
not claimed as a proof of either side. No publication hypothesis is a consumer. -/
theorem publication_iff_original_integral_mass :
    publicationTarget ≤ Wu08TerminalAlignment.firstMain ↔
      publicationTarget/8-log (1127/200) ≤
        Wu08OriginalFirstSteps.C (1327/200)+Wu08OriginalFirstSteps.E (1327/200) := by
  unfold Wu08TerminalAlignment.firstMain
  constructor <;> intro h <;> linarith only [h]

end FirstPublicationAudit
