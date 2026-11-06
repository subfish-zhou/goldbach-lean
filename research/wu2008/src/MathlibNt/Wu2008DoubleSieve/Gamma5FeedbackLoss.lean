import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackBounds

namespace Wu2008DoubleSieve

open Real Set MeasureTheory
open scoped Classical Topology Interval

theorem gamma5Feedback_middle_difference {v : ℝ}
    (hv : v ∈ Icc gamma5FeedbackVc gamma5FeedbackVe) :
    gamma5FeedbackLegalMiddle v = gamma5FeedbackB v - gamma5FeedbackR v := by
  have hg := gamma5Feedback_middle_geometry hv
  have hb := gamma5Feedback_B_geometry hg.1
  have hb0 : 0 < gamma5ClassicalB := by norm_num [gamma5ClassicalB]
  have h1 : 0 < gamma5ClassicalB / (gamma5FeedbackW v - gamma5ClassicalB) :=
    div_pos hb0 hb.2.1
  have h2 : 0 < (gamma5ClassicalS - 2 * v) / v := div_pos hg.2.2.2 hb.1
  rw [gamma5FeedbackB, gamma5FeedbackR, gamma5Feedback_B_ratio, ← mul_sub, ← log_div h1.ne' h2.ne']
  unfold gamma5FeedbackLegalMiddle
  congr 2
  change gamma5ClassicalB * v /
    ((gamma5FeedbackW v - gamma5ClassicalB) * (gamma5ClassicalS - 2 * v)) = _
  have hv0 := hb.1.ne'
  have hd0 := hb.2.1.ne'
  have hs0 := hg.2.2.2.ne'
  field_simp

/-- D5 already contains the factor one fifth; the count kernel does not. -/
theorem gamma5Feedback_kernel_identity (v : ℝ) :
    gamma5FeedbackLegalKernel v = gamma5FeedbackFullKernel v - 5 * gamma5FeedbackLossKernel v := by
  have ho := gamma5Feedback_breakpoints
  have hmc : gamma5FeedbackVm < gamma5FeedbackVc := ho.2.2.2.2.2.2.1
  have hce : gamma5FeedbackVc < gamma5FeedbackVe := ho.2.2.2.2.2.2.2.1
  have hef : gamma5FeedbackVe < gamma5FeedbackVf := ho.2.2.2.2.2.2.2.2.1
  by_cases hmid : gamma5FeedbackVc < v ∧ v < gamma5FeedbackVe
  · have hb : gamma5FeedbackVm ≤ v ∧ v ≤ gamma5FeedbackVf := ⟨by linarith, by linarith⟩
    have hnot : ¬(gamma5FeedbackVm ≤ v ∧ v ≤ gamma5FeedbackVc) := by
      intro h; linarith [h.2, hmid.1]
    rw [gamma5FeedbackLegalKernel, if_pos hmid, gamma5FeedbackFullKernel, if_pos hb,
      gamma5FeedbackLossKernel, if_neg hnot, if_pos hmid,
      gamma5Feedback_middle_difference ⟨hmid.1.le, hmid.2.le⟩]
    ring
  · by_cases hlow : gamma5FeedbackVm ≤ v ∧ v ≤ gamma5FeedbackVc
    · have hb : gamma5FeedbackVm ≤ v ∧ v ≤ gamma5FeedbackVf := ⟨hlow.1, by linarith [hlow.2]⟩
      have hn1 : ¬(gamma5FeedbackVe ≤ v ∧ v ≤ gamma5FeedbackVf) := by
        intro h; linarith [h.1, hlow.2]
      have hn2 : ¬(gamma5FeedbackVf < v ∧ v ≤ gamma5FeedbackVp) := by
        intro h; linarith [h.1, hlow.2]
      rw [gamma5FeedbackLegalKernel, if_neg hmid, if_neg hn1, if_neg hn2,
        gamma5FeedbackFullKernel, if_pos hb, gamma5FeedbackLossKernel, if_pos hlow]
      ring
    · have heq : (gamma5FeedbackVe ≤ v ∧ v ≤ gamma5FeedbackVf) ↔
          (gamma5FeedbackVm ≤ v ∧ v ≤ gamma5FeedbackVf) := by
        constructor
        · exact fun h => ⟨by linarith [h.1], h.2⟩
        · intro h
          have hvc : gamma5FeedbackVc < v := by
            by_contra hn; exact hlow ⟨h.1, le_of_not_gt hn⟩
          have hve : gamma5FeedbackVe ≤ v := by
            by_contra hn; exact hmid ⟨hvc, lt_of_not_ge hn⟩
          exact ⟨hve, h.2⟩
      simp only [gamma5FeedbackLegalKernel, if_neg hmid, gamma5FeedbackFullKernel,
        gamma5FeedbackLossKernel, if_neg hlow, mul_zero, sub_zero, heq]




end Wu2008DoubleSieve
