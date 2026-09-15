import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerPositive

namespace Wu2008DoubleSieve.SecondFunctionalSmallDelta
open Set MeasureTheory SecondFunctionalParameters SecondFunctionalSignedCore
open SecondFunctionalRationalCost
open scoped Interval

/-- Only the actual signed cost depends on delta; its rational cap controls the loss. -/
theorem row4_D_strict {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) :
    (1/60 : ℝ) < D row4 δ := by
  have hd : 0 < 1 - 2*δ := by linarith

  have hS := positiveKernel_original_strict_lower (a := row4.s) (b := row4.S)
    (by norm_num [row4]) (by norm_num [row4])
    (by norm_num [row4]) (by norm_num [row4])
  have hk := positiveKernel_original_strict_lower (a := row4.kappa3) (b := row4.kappa1)
    (by norm_num [row4]) (by norm_num [row4])
    (by norm_num [row4]) (by norm_num [row4])
  have hl := directedL_upper (c := row4.kappa2)
    (by norm_num [row4]) (by norm_num [row4])
  have hc := row4_cost_upper
  have hp0 : 0 ≤ 2 / (1 - 2*δ) := by positivity
  have hp1 : 2 / (1 - 2*δ) ≤ (2 : ℝ) / (1 - 2*(1/1000)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hcost := (mul_le_mul_of_nonneg_left hc hp0).trans
    (mul_le_mul_of_nonneg_right hp1 (by norm_num : (0 : ℝ) ≤ 31667784024997/755387500000000))
  norm_num only [row4] at hS hk hl hcost
  dsimp only [D, row4]
  norm_num at hS hk hl ⊢
  linarith only [hS, hk, hl, hcost]

/-- The actual core-to-H theorem supplies the uniform positive seed. -/
theorem row4_H_strict {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) :
    (1/300 : ℝ) < wuImprovementLimit true δ (5/2) := by
  have h := SecondFunctionalStrictMargins.actual_core_lower (3 : Fin 4) hδ (by linarith)
  change D row4 δ / 5 ≤ wuImprovementLimit true δ row4.s at h
  rw [(show row4.s = (5/2 : ℝ) by norm_num [row4])] at h
  linarith only [h, row4_D_strict hδ hδhi]

/-- Antitonicity is only in the original s variable, never in delta. -/
theorem H_strict {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000)
    (hs : 1 ≤ s) (hsHi : s ≤ 5/2) :
    (1/300 : ℝ) < wuImprovementLimit true δ s := by
  have hm := wuImprovementLimit_upper_antitone_initial hδ (by linarith)
    (show s ∈ Icc 1 3 from ⟨hs, by linarith⟩)
    (show (5/2 : ℝ) ∈ Icc 1 3 by norm_num) hsHi
  exact (row4_H_strict hδ hδhi).trans_le hm

/-- The actual upper-gain kernel is integrable; no continuity of H is assumed. -/
theorem actual_kernel_integrable {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) (hs : 2 ≤ s) (ht : s ≤ 7/2) :
    IntervalIntegrable (fun u => wuImprovementLimit true δ u / u)
      volume (s-1) (5/2) :=
  wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
    (by linarith) (by linarith) (by norm_num)

/-- The original cross inequality transfers the upper seed into a lower gain. -/
theorem h_strict {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) (hs : 2 ≤ s) (ht : s < 7/2) :
    (7/2-s)/750 < wuImprovementLimit false δ s := by
  have hab : s-1 ≤ (5/2 : ℝ) := by linarith
  have hc : ContinuousOn (fun u : ℝ => (1/300 : ℝ)/u) (Icc (s-1) (5/2)) :=
    continuousOn_const.div continuousOn_id (fun u hu => by change u ≠ 0; linarith [hu.1])
  have hi := intervalIntegral.integral_mono_on hab
    (hc.intervalIntegrable_of_Icc hab) (actual_kernel_integrable hδ hδhi hs ht.le)
    (fun u hu => div_le_div_of_nonneg_right
      (H_strict hδ hδhi (by linarith [hu.1]) hu.2).le
      (by linarith [hu.1]))
  have he : (∫ u in (s-1)..(5/2 : ℝ), (1/300 : ℝ)/u) =
      (1/300 : ℝ) * ∫ u in (s-1)..(5/2 : ℝ), 1/u := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    ring
  rw [he] at hi
  have hr := SecondFunctionalLowerPositive.reciprocal_integral_strict hs ht
  have hn := wuImprovementLimit_nonneg false (δ := δ) (s := (7/2 : ℝ))
    hδ (by linarith) (by norm_num) (by norm_num)
  have hx := wuImprovementLimit_lower_cross (δ := δ) (s := s)
    (t := (7/2 : ℝ)) hδ (by linarith) hs ht.le (by norm_num)
  norm_num only at hx
  linarith

end Wu2008DoubleSieve.SecondFunctionalSmallDelta
