import NodeFubini

namespace NodeExtension
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval

/-- The actual upper gain after two genuine cross inequalities and triangular Fubini. -/
theorem actual_upper_log {δ v : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    wuImprovementLimit false δ 4 * log (4 / (v - 1)) +
      (∫ t in (v - 2)..3, wuImprovementLimit true δ t / t *
        log ((t + 1) / (v - 1))) ≤ wuImprovementLimit true δ v := by
  have hp := wuImprovementLimit_div_intervalIntegrable true hd
    (by linarith : δ < 1 / 2) (a := v - 2) (b := 3)
    (by linarith) (by linarith) (by norm_num)
  have hs := shifted_tail (by linarith : 0 < (v - 2) + 1)
    (by linarith : v - 2 ≤ 3) hp (wuImprovementLimit false δ 4)
  have hvnorm : v - 2 + 1 = v - 1 := by ring
  norm_num only [hvnorm, show (3 : ℝ) + 1 = 4 by norm_num] at hs
  have hhi := wuImprovementLimit_div_intervalIntegrable false hd
    (by linarith : δ < 1 / 2) (a := v - 1) (b := 4)
    (by linarith) (by linarith) (by norm_num)
  have hm := intervalIntegral.integral_mono_on (by linarith : v - 1 ≤ 4) hs.1 hhi
    (fun x hx => div_le_div_of_nonneg_right
      (by
        have h := wuImprovementLimit_lower_cross hd hdhi (s := x) (t := 4)
          (by linarith [hx.1]) hx.2 (by norm_num)
        norm_num at h
        exact h) (by linarith [hx.1] : 0 ≤ x))
  rw [hs.2] at hm
  have hu := wuImprovementLimit_upper_cross hd hdhi (s := v) (t := 5)
    (by linarith) hv5 (by norm_num)
  norm_num at hu
  have hn := wuImprovementLimit_nonneg true hd (by linarith : δ < 1 / 2)
    (s := 5) (by norm_num) (by norm_num)
  linarith

noncomputable def sigma0 (t : ℝ) : ℝ := sigma 3 (t + 2) (t + 1) / (1 - D0)
noncomputable def aProfile (f : ℝ → ℝ) : ℝ := ∫ t in (1 : ℝ)..3, f t * sigma0 t / t
noncomputable def gProfile (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  aProfile f + ∫ t in (u - 1)..3, f t / t
noncomputable def eProfile (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  aProfile f * log (4 / (v - 1)) +
    ∫ t in (v - 2)..3, f t / t * log ((t + 1) / (v - 1))

theorem log_weight_continuous {v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    ContinuousOn (fun t => log ((t + 1) / (v - 1))) (uIcc (v - 2) 3) := by
  rw [uIcc_of_le (by linarith : v - 2 ≤ 3)]
  apply ContinuousOn.log
  · exact (continuousOn_id.add continuousOn_const).div_const _
  · intro t ht
    exact ne_of_gt (div_pos (by linarith [ht.1]) (by linarith))

theorem profile_div_integrable {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3) :
    IntervalIntegrable (fun t => f t / t) volume 1 3 := by
  simpa only [mul_one_div] using hf.mul_continuousOn
    (reciprocal_continuous (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 3))

theorem profile_subinterval {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {a : ℝ} (ha : 1 ≤ a) (ha3 : a ≤ 3) : IntervalIntegrable f volume a 3 := by
  apply hf.mono_set
  rw [uIcc_of_le ha3, uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
  exact Icc_subset_Icc ha le_rfl

theorem profile_upper_log {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    (hfH : ∀ t ∈ Icc (1 : ℝ) 3, f t ≤ wuImprovementLimit true δ t)
    {v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    wuImprovementLimit false δ 4 * log (4 / (v - 1)) +
      (∫ t in (v - 2)..3, f t / t * log ((t + 1) / (v - 1))) ≤
        wuImprovementLimit true δ v := by
  have hi := (profile_subinterval (profile_div_integrable hf)
    (by linarith : 1 ≤ v - 2) (by linarith : v - 2 ≤ 3)).mul_continuousOn
    (log_weight_continuous hv hv5)
  have hH := (wuImprovementLimit_div_intervalIntegrable true hd
    (by linarith : δ < 1 / 2) (a := v - 2) (b := 3)
    (by linarith) (by linarith) (by norm_num)).mul_continuousOn
    (log_weight_continuous hv hv5)
  have hm := intervalIntegral.integral_mono_on (by linarith : v - 2 ≤ 3) hi hH
    (fun t ht => mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hfH t ⟨by linarith [ht.1], ht.2⟩)
        (by linarith [ht.1]))
      (log_nonneg ((le_div_iff₀ (by linarith : 0 < v - 1)).2 (by linarith [ht.1]))))
  exact (add_le_add le_rfl hm).trans (actual_upper_log hd hdhi hv hv5)

theorem aProfile_eq (f : ℝ → ℝ) : aProfile f =
    (∫ t in (1 : ℝ)..3, f t / t * sigma 3 (t + 2) (t + 1)) / (1 - D0) := by
  rw [aProfile, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [sigma0]
  ring

/-- Feedback elimination for the actual h(4); all cross and triangular inputs are proved above. -/
theorem profile_feedback {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    (hfH : ∀ t ∈ Icc (1 : ℝ) 3, f t ≤ wuImprovementLimit true δ t) :
    aProfile f ≤ wuImprovementLimit false δ 4 := by
  let c := wuImprovementLimit false δ 4
  have hs := sigma_feedback (profile_div_integrable hf)
  have hi1 := (sigma_integrable (by norm_num : (1 : ℝ) < 3)
    (by norm_num : (3 : ℝ) ≤ 5) (by norm_num : (0 : ℝ) < 4)).const_mul c
  have hiH := wuImprovementLimit_div_intervalIntegrable true hd
    (by linarith : δ < 1 / 2) (a := 3) (b := 5)
    (by norm_num) (by norm_num) (by norm_num)
  have hm := intervalIntegral.integral_mono_on (by norm_num : (3 : ℝ) ≤ 5)
    (hi1.add hs.1) hiH (fun v hv => by
      have h := div_le_div_of_nonneg_right (profile_upper_log hd hdhi hf hfH hv.1 hv.2)
        (by linarith [hv.1] : 0 ≤ v)
      dsimp [c] at *
      convert h using 1 <;> first | rfl | ring)
  rw [intervalIntegral.integral_add hi1 hs.1, intervalIntegral.integral_const_mul, hs.2] at hm
  have hc := actual_h4_tail hd hdhi
  change c * D0 + _ ≤ _ at hm
  rw [aProfile_eq]
  apply (div_le_iff₀ (sub_pos.mpr D0_lt_one)).2
  dsimp [c] at hm
  nlinarith

/-- Continuous extension for every integrable profile below the actual upper gain. -/
theorem profile_extension {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    (hfH : ∀ t ∈ Icc (1 : ℝ) 3, f t ≤ wuImprovementLimit true δ t) :
    aProfile f ≤ wuImprovementLimit false δ 4 ∧
    (∀ u ∈ Icc (2 : ℝ) 4, gProfile f u ≤ wuImprovementLimit false δ u) ∧
    (∀ v ∈ Icc (3 : ℝ) 5, eProfile f v ≤ wuImprovementLimit true δ v) := by
  have ha := profile_feedback hd hdhi hf hfH
  refine ⟨ha, ?_, ?_⟩
  · intro u hu
    have hm := intervalIntegral.integral_mono_on (by linarith [hu.2] : u - 1 ≤ 3)
      (profile_subinterval (profile_div_integrable hf) (by linarith [hu.1]) (by linarith [hu.2]))
      (wuImprovementLimit_div_intervalIntegrable true hd (by linarith : δ < 1 / 2)
        (a := u - 1) (b := 3) (by linarith [hu.1]) (by linarith [hu.2]) (by norm_num))
      (fun t ht => div_le_div_of_nonneg_right
        (hfH t ⟨by linarith [hu.1, ht.1], ht.2⟩) (by linarith [hu.1, ht.1]))
    have hc := wuImprovementLimit_lower_cross hd hdhi hu.1 hu.2 (by norm_num : (4 : ℝ) ≤ 10)
    norm_num at hc
    exact (add_le_add ha hm).trans hc
  · intro v hv
    have hl : 0 ≤ log (4 / (v - 1)) :=
      log_nonneg ((le_div_iff₀ (by linarith [hv.1] : 0 < v - 1)).2 (by linarith [hv.2]))
    exact (add_le_add (mul_le_mul_of_nonneg_right ha hl) le_rfl).trans
      (profile_upper_log hd hdhi hf hfH hv.1 hv.2)

/-- No integrability hypothesis: it is supplied by the profile's antitonicity. -/
theorem antitone_extension {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {f : ℝ → ℝ} (hf : AntitoneOn f (Icc (1 : ℝ) 3))
    (hfH : ∀ t ∈ Icc (1 : ℝ) 3, f t ≤ wuImprovementLimit true δ t) :
    aProfile f ≤ wuImprovementLimit false δ 4 ∧
    (∀ u ∈ Icc (2 : ℝ) 4, gProfile f u ≤ wuImprovementLimit false δ u) ∧
    (∀ v ∈ Icc (3 : ℝ) 5, eProfile f v ≤ wuImprovementLimit true δ v) := by
  apply profile_extension hd hdhi _ hfH
  apply AntitoneOn.intervalIntegrable
  simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] using hf

/-- The continuous extension applied to the actual H itself. -/
theorem actual_continuous_extension {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10) :
    aProfile (wuImprovementLimit true δ) ≤ wuImprovementLimit false δ 4 ∧
    (∀ u ∈ Icc (2 : ℝ) 4, gProfile (wuImprovementLimit true δ) u ≤ wuImprovementLimit false δ u) ∧
    (∀ v ∈ Icc (3 : ℝ) 5, eProfile (wuImprovementLimit true δ) v ≤ wuImprovementLimit true δ v) := by
  exact profile_extension hd hdhi
    (wuImprovementLimit_intervalIntegrable true hd (by linarith : δ < 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)) (fun _ _ => le_rfl)

theorem sigma0_nonneg {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 3) : 0 ≤ sigma0 t := by
  apply div_nonneg _ (sub_pos.mpr D0_lt_one).le
  apply intervalIntegral.integral_nonneg (by linarith [ht.1])
  intro v hv
  apply div_nonneg
  · apply log_nonneg
    apply (le_div_iff₀ (by linarith [hv.1] : 0 < v - 1)).2
    linarith [hv.2]
  · linarith [hv.1]

theorem profiles_nonneg {f : ℝ → ℝ} (hf : ∀ t ∈ Icc (1 : ℝ) 3, 0 ≤ f t) :
    0 ≤ aProfile f ∧ (∀ u ∈ Icc (2 : ℝ) 4, 0 ≤ gProfile f u) ∧
      (∀ v ∈ Icc (3 : ℝ) 5, 0 ≤ eProfile f v) := by
  have ha : 0 ≤ aProfile f := by
    apply intervalIntegral.integral_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    intro t ht
    exact div_nonneg (mul_nonneg (hf t ht) (sigma0_nonneg ht)) (by linarith [ht.1])
  refine ⟨ha, ?_, ?_⟩
  · intro u hu
    apply add_nonneg ha
    apply intervalIntegral.integral_nonneg (by linarith [hu.2])
    intro t ht
    exact div_nonneg (hf t ⟨by linarith [hu.1, ht.1], ht.2⟩) (by linarith [hu.1, ht.1])
  · intro v hv
    apply add_nonneg
    · apply mul_nonneg ha
      exact log_nonneg ((le_div_iff₀ (by linarith [hv.1] : 0 < v - 1)).2 (by linarith [hv.2]))
    · apply intervalIntegral.integral_nonneg (by linarith [hv.2])
      intro t ht
      apply mul_nonneg
      · exact div_nonneg (hf t ⟨by linarith [hv.1, ht.1], ht.2⟩)
          (by linarith [hv.1, ht.1])
      · exact log_nonneg ((le_div_iff₀ (by linarith [hv.1] : 0 < v - 1)).2 (by linarith [ht.1]))

end NodeExtension
