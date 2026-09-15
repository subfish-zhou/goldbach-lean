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
  dsimp [gamma5FeedbackW]
  ring

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

theorem gamma5Feedback_loss_bounds (v : ℝ) :
    0 ≤ gamma5FeedbackLossKernel v ∧ gamma5FeedbackLossKernel v ≤ 20 := by
  have hb := gamma5Feedback_full_legal_bounds v
  have he := gamma5Feedback_kernel_identity v
  constructor <;> linarith

theorem gamma5Feedback_loss_integrable : Integrable gamma5FeedbackLossKernel := by
  have he : gamma5FeedbackLossKernel =
      fun v => (gamma5FeedbackFullKernel v - gamma5FeedbackLegalKernel v) / 5 := by
    funext v
    have := gamma5Feedback_kernel_identity v
    linarith
  rw [he]
  exact (gamma5Feedback_full_integrable.sub gamma5Feedback_legal_integrable).div_const 5

theorem gamma5Feedback_kernel_support :
    Function.support gamma5FeedbackFullKernel ⊆ Icc gamma5FeedbackVm gamma5FeedbackVp ∧
    Function.support gamma5FeedbackLegalKernel ⊆ Icc gamma5FeedbackVc gamma5FeedbackVp ∧
    Function.support gamma5FeedbackLossKernel ⊆ Icc gamma5FeedbackVm gamma5FeedbackVe := by
  have ho := gamma5Feedback_breakpoints
  have hmc : gamma5FeedbackVm < gamma5FeedbackVc := ho.2.2.2.2.2.2.1
  have hce : gamma5FeedbackVc < gamma5FeedbackVe := ho.2.2.2.2.2.2.2.1
  have hef : gamma5FeedbackVe < gamma5FeedbackVf := ho.2.2.2.2.2.2.2.2.1
  have hfp : gamma5FeedbackVf < gamma5FeedbackVp := ho.2.2.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    by_contra hn
    exact hv ((gamma5Feedback_full_slice v).symm.trans (gamma5Feedback_slice_outside hn))
  · intro v hv
    by_contra hn
    have hn1 : ¬(gamma5FeedbackVc < v ∧ v < gamma5FeedbackVe) :=
      fun h => hn ⟨h.1.le, by linarith [h.2]⟩
    have hn2 : ¬(gamma5FeedbackVe ≤ v ∧ v ≤ gamma5FeedbackVf) :=
      fun h => hn ⟨by linarith [h.1], h.2.trans hfp.le⟩
    have hn3 : ¬(gamma5FeedbackVf < v ∧ v ≤ gamma5FeedbackVp) :=
      fun h => hn ⟨by linarith [h.1], h.2⟩
    exact hv (by simp only [gamma5FeedbackLegalKernel, if_neg hn1, if_neg hn2, if_neg hn3])
  · intro v hv
    by_contra hn
    have hn1 : ¬(gamma5FeedbackVm ≤ v ∧ v ≤ gamma5FeedbackVc) :=
      fun h => hn ⟨h.1, h.2.trans hce.le⟩
    have hn2 : ¬(gamma5FeedbackVc < v ∧ v < gamma5FeedbackVe) :=
      fun h => hn ⟨hmc.le.trans h.1.le, h.2.le⟩
    exact hv (by simp only [gamma5FeedbackLossKernel, if_neg hn1, if_neg hn2])

end Wu2008DoubleSieve
