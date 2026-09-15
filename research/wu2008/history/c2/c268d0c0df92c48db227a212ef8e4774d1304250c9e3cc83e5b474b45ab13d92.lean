import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackKernel

namespace Wu2008DoubleSieve

open Real Set MeasureTheory
open scoped Classical Topology Interval

theorem gamma5Feedback_slice_interval {legal : Bool} {v A B : ℝ}
    (hs : ∀ t, gamma5FeedbackSlice legal v t ↔ A ≤ t ∧ t ≤ B) (hAB : A ≤ B) :
    (∫ t : ℝ, gamma5FeedbackMasked legal v t) =
      ∫ t in A..B, gamma5FeedbackDensity v t := by
  simp_rw [gamma5FeedbackMasked, hs]
  exact gamma5Feedback_mask_interval _ hAB

theorem gamma5Feedback_slice_outside {legal : Bool} {v : ℝ}
    (hv : v ∉ Icc gamma5FeedbackVm gamma5FeedbackVp) :
    (∫ t : ℝ, gamma5FeedbackMasked legal v t) = 0 := by
  have h (t : ℝ) : ¬gamma5FeedbackSlice legal v t :=
    fun ht => hv (gamma5Feedback_slice_bounds ht).1
  simp only [gamma5FeedbackMasked, if_neg (h _), integral_zero]

theorem gamma5Feedback_B_geometry {v : ℝ}
    (hv : v ∈ Icc gamma5FeedbackVm gamma5FeedbackVf) :
    0 < v ∧ 0 < gamma5FeedbackW v - gamma5ClassicalB ∧
    gamma5MassA ≤ gamma5FeedbackW v - gamma5ClassicalB ∧
    gamma5FeedbackW v - gamma5ClassicalB ≤ gamma5FeedbackW v / 2 ∧
    gamma5FeedbackW v / 2 < gamma5FeedbackW v := by
  rcases hv with ⟨hl, hu⟩
  norm_num [gamma5FeedbackVm, gamma5FeedbackVf, gamma5FeedbackW,
    gamma5ClassicalS, gamma5ClassicalB, gamma5MassA] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem gamma5Feedback_A_geometry {v : ℝ}
    (hv : v ∈ Icc gamma5FeedbackVf gamma5FeedbackVp) :
    0 < v ∧ 0 < gamma5MassA ∧ gamma5FeedbackW v - gamma5ClassicalB ≤ gamma5MassA ∧
    gamma5MassA ≤ gamma5FeedbackW v / 2 ∧
    gamma5FeedbackW v / 2 < gamma5FeedbackW v ∧
    gamma5FeedbackW v / 2 ≤ v / gamma5ClassicalS := by
  rcases hv with ⟨hl, hu⟩
  norm_num [gamma5FeedbackVp, gamma5FeedbackVf, gamma5FeedbackW,
    gamma5ClassicalS, gamma5ClassicalB, gamma5MassA] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem gamma5Feedback_B_integral {v : ℝ}
    (hv : v ∈ Icc gamma5FeedbackVm gamma5FeedbackVf) :
    (∫ t in (gamma5FeedbackW v - gamma5ClassicalB)..(gamma5FeedbackW v / 2),
      gamma5FeedbackDensity v t) = gamma5FeedbackB v := by
  have hg := gamma5Feedback_B_geometry hv
  rw [gamma5Feedback_density_integral hg.2.1 hg.2.2.2.1 hg.2.2.2.2,
    gamma5FeedbackB, gamma5Feedback_B_ratio]
  congr 2
  have hw : gamma5FeedbackW v ≠ 0 := by linarith [hg.2.2.2.2]
  field_simp
  ring

theorem gamma5Feedback_A_integral {v : ℝ}
    (hv : v ∈ Icc gamma5FeedbackVf gamma5FeedbackVp) :
    (∫ t in gamma5MassA..(gamma5FeedbackW v / 2), gamma5FeedbackDensity v t) =
      gamma5FeedbackA v := by
  have hg := gamma5Feedback_A_geometry hv
  rw [gamma5Feedback_density_integral hg.2.1 hg.2.2.2.1 hg.2.2.2.2.1, gamma5FeedbackA]
  congr 2
  have hw : gamma5FeedbackW v ≠ 0 := by linarith [hg.2.2.2.2.1]
  rw [show gamma5FeedbackW v - gamma5FeedbackW v / 2 = gamma5FeedbackW v / 2 by ring]
  rw [mul_comm (gamma5FeedbackW v / 2),
    mul_div_mul_right _ _ (div_ne_zero hw (by norm_num))]
  norm_num [gamma5MassA, gamma5ClassicalS, gamma5FeedbackW]
  ring

theorem gamma5Feedback_full_slice (v : ℝ) :
    (∫ t : ℝ, gamma5FeedbackMasked false v t) = gamma5FeedbackFullKernel v := by
  by_cases hb : gamma5FeedbackVm ≤ v ∧ v ≤ gamma5FeedbackVf
  · have hg := gamma5Feedback_B_geometry hb
    rw [gamma5FeedbackFullKernel, if_pos hb]
    rw [gamma5Feedback_slice_interval (A := gamma5FeedbackW v - gamma5ClassicalB)
      (B := gamma5FeedbackW v / 2) (fun t => ?_) hg.2.2.2.1]
    · exact gamma5Feedback_B_integral hb
    · simp only [gamma5FeedbackSlice, Bool.false_eq_true, false_implies, and_true]
      constructor
      · exact fun h => ⟨h.2.2, h.2.1⟩
      · exact fun h => ⟨hg.2.2.1.trans h.1, h.2, h.1⟩
  · by_cases ha : gamma5FeedbackVf < v ∧ v ≤ gamma5FeedbackVp
    · have hg := gamma5Feedback_A_geometry ⟨ha.1.le, ha.2⟩
      rw [gamma5FeedbackFullKernel, if_neg hb, if_pos ha]
      rw [gamma5Feedback_slice_interval (A := gamma5MassA)
        (B := gamma5FeedbackW v / 2) (fun t => ?_) hg.2.2.2.1]
      · exact gamma5Feedback_A_integral ⟨ha.1.le, ha.2⟩
      · simp only [gamma5FeedbackSlice, Bool.false_eq_true, false_implies, and_true]
        constructor
        · exact fun h => ⟨h.1, h.2.1⟩
        · exact fun h => ⟨h.1, h.2, hg.2.2.1.trans h.1⟩
    · rw [gamma5FeedbackFullKernel, if_neg hb, if_neg ha]
      apply gamma5Feedback_slice_outside
      intro h
      by_cases hh : v ≤ gamma5FeedbackVf
      · exact hb ⟨h.1, hh⟩
      · exact ha ⟨lt_of_not_ge hh, h.2⟩

theorem gamma5Feedback_middle_geometry {v : ℝ}
    (hv : v ∈ Icc gamma5FeedbackVc gamma5FeedbackVe) :
    v ∈ Icc gamma5FeedbackVm gamma5FeedbackVf ∧
    gamma5FeedbackW v - gamma5ClassicalB ≤ v / gamma5ClassicalS ∧
    v / gamma5ClassicalS ≤ gamma5FeedbackW v / 2 ∧
    0 < gamma5ClassicalS - 2 * v := by
  rcases hv with ⟨hl, hu⟩
  norm_num [gamma5FeedbackVm, gamma5FeedbackVc, gamma5FeedbackVe, gamma5FeedbackVf,
    gamma5FeedbackW, gamma5ClassicalS, gamma5ClassicalB, gamma5MassA] at *
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith, by linarith⟩

theorem gamma5Feedback_middle_integral {v : ℝ}
    (hv : v ∈ Icc gamma5FeedbackVc gamma5FeedbackVe) :
    (∫ t in (gamma5FeedbackW v - gamma5ClassicalB)..(v / gamma5ClassicalS),
      gamma5FeedbackDensity v t) = gamma5FeedbackLegalMiddle v := by
  have hg := gamma5Feedback_middle_geometry hv
  have hb := gamma5Feedback_B_geometry hg.1
  rw [gamma5Feedback_density_integral hb.2.1 hg.2.1
    (hg.2.2.1.trans_lt hb.2.2.2.2), gamma5FeedbackLegalMiddle]
  congr 2
  dsimp [gamma5FeedbackW]
  have hS : gamma5ClassicalS ≠ 0 := by norm_num [gamma5ClassicalS]
  field_simp
  ring

theorem gamma5Feedback_legal_slice (v : ℝ) :
    (∫ t : ℝ, gamma5FeedbackMasked true v t) = gamma5FeedbackLegalKernel v := by
  by_cases hm : gamma5FeedbackVc < v ∧ v < gamma5FeedbackVe
  · have hg := gamma5Feedback_middle_geometry ⟨hm.1.le, hm.2.le⟩
    have hb := gamma5Feedback_B_geometry hg.1
    rw [gamma5FeedbackLegalKernel, if_pos hm]
    rw [gamma5Feedback_slice_interval (A := gamma5FeedbackW v - gamma5ClassicalB)
      (B := v / gamma5ClassicalS) (fun t => ?_) hg.2.1]
    · exact gamma5Feedback_middle_integral ⟨hm.1.le, hm.2.le⟩
    · simp only [gamma5FeedbackSlice, true_implies]
      constructor
      · exact fun h => ⟨h.2.2.1, h.2.2.2⟩
      · exact fun h => ⟨hb.2.2.1.trans h.1, h.2.trans hg.2.2.1, h.1, h.2⟩
  · by_cases hb : gamma5FeedbackVe ≤ v ∧ v ≤ gamma5FeedbackVf
    · have hbounds : v ∈ Icc gamma5FeedbackVm gamma5FeedbackVf := by
        have ho := gamma5Feedback_breakpoints
        exact ⟨by linarith [ho.2.2.2.2.2.2.1, ho.2.2.2.2.2.2.2.1], hb.2⟩
      have hg := gamma5Feedback_B_geometry hbounds
      have hu : gamma5FeedbackW v / 2 ≤ v / gamma5ClassicalS := by
        have := hb.1
        norm_num [gamma5FeedbackVe, gamma5FeedbackW, gamma5ClassicalS] at *
        linarith
      rw [gamma5FeedbackLegalKernel, if_neg hm, if_pos hb]
      rw [gamma5Feedback_slice_interval (A := gamma5FeedbackW v - gamma5ClassicalB)
        (B := gamma5FeedbackW v / 2) (fun t => ?_) hg.2.2.2.1]
      · exact gamma5Feedback_B_integral hbounds
      · simp only [gamma5FeedbackSlice, true_implies]
        constructor
        · exact fun h => ⟨h.2.2.1, h.2.1⟩
        · exact fun h => ⟨hg.2.2.1.trans h.1, h.2, h.1, h.2.trans hu⟩
    · by_cases ha : gamma5FeedbackVf < v ∧ v ≤ gamma5FeedbackVp
      · have hg := gamma5Feedback_A_geometry ⟨ha.1.le, ha.2⟩
        rw [gamma5FeedbackLegalKernel, if_neg hm, if_neg hb, if_pos ha]
        rw [gamma5Feedback_slice_interval (A := gamma5MassA)
          (B := gamma5FeedbackW v / 2) (fun t => ?_) hg.2.2.2.1]
        · exact gamma5Feedback_A_integral ⟨ha.1.le, ha.2⟩
        · simp only [gamma5FeedbackSlice, true_implies]
          constructor
          · exact fun h => ⟨h.1, h.2.1⟩
          · exact fun h => ⟨h.1, h.2, hg.2.2.1.trans h.1, h.2.trans hg.2.2.2.2.2⟩
      · rw [gamma5FeedbackLegalKernel, if_neg hm, if_neg hb, if_neg ha]
        by_cases hv : v ∈ Icc gamma5FeedbackVm gamma5FeedbackVp
        · have hvc : v ≤ gamma5FeedbackVc := by
            have ho := gamma5Feedback_breakpoints
            by_contra h
            have h' : gamma5FeedbackVc < v := lt_of_not_ge h
            have hve : gamma5FeedbackVe ≤ v := by
              by_contra hve; exact hm ⟨h', lt_of_not_ge hve⟩
            have hvf : gamma5FeedbackVf < v := by
              by_contra hvf; exact hb ⟨hve, le_of_not_gt hvf⟩
            exact ha ⟨hvf, hv.2⟩
          have hzero : ∀ᵐ t : ℝ, gamma5FeedbackMasked true v t = 0 := by
            filter_upwards [show ∀ᵐ t : ℝ, t ≠ v / gamma5ClassicalS from
              ae_iff.mpr (by simp)] with t ht
            apply if_neg
            intro h
            have hh := h.2.2.2 rfl
            have hl := h.2.2.1
            have hle : v / gamma5ClassicalS ≤ gamma5FeedbackW v - gamma5ClassicalB := by
              norm_num [gamma5FeedbackVc, gamma5FeedbackW, gamma5ClassicalS,
                gamma5ClassicalB] at hvc ⊢
              linarith
            exact ht (le_antisymm hh (hle.trans hl))
          exact (integral_congr_ae hzero).trans (integral_zero _ _)
        · exact gamma5Feedback_slice_outside hv

end Wu2008DoubleSieve
