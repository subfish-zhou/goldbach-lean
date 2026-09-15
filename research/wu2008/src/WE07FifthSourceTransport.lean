import WE07FifthClassicalRoot

namespace WuTarget.Wu08FifthSource
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open scoped Interval
noncomputable section

def paperKernel (t u : ℝ) : ℝ :=
  wuLowerCoefficient u/(t*u*(1-2*t-2*a*u))

def paperClassical : ℝ :=
  8*∫ t in a..b, ∫ u in ((1/2-b-t)/a)..((1/2-2*t)/a), paperKernel t u

theorem parameters_exact : a = (100/1327 : ℝ) ∧ b = (25/206 : ℝ) := by
  norm_num [a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem coefficient_initial {s : ℝ} (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    wuLowerCoefficient s = log (s-1) := by
  linarith only [ClassicalLossBottleneck.initial_exact hs hs4]

theorem coefficient_recurrence {s : ℝ} (hs : 4 ≤ s) (hs6 : s ≤ 6) :
    wuLowerCoefficient s = log (s-1)+
      ∫ t in (3 : ℝ)..(s-1), (∫ u in (2 : ℝ)..(t-1), log (u-1)/u)/t := by
  rw [Wu08OriginalFirstSteps.lower_middle hs hs6, Wu08OriginalFirstSteps.C_literal hs]

theorem parameter_range {t u : ℝ} (ht : t ∈ Icc a b)
    (hu : u ∈ Icc ((1/2-b-t)/a) ((1/2-2*t)/a)) :
    s0 ≤ u ∧ u ≤ FifthClassicalShape.q := by
  have ha : 0 < a := truncatedSixthLower_parameters.1
  have hlo : s0 ≤ (1/2-b-t)/a := by
    unfold s0
    apply div_le_div_of_nonneg_right _ ha.le
    linarith [ht.2]
  have hhi : (1/2-2*t)/a ≤ FifthClassicalShape.q := by
    unfold FifthClassicalShape.q
    apply div_le_div_of_nonneg_right _ ha.le
    linarith [ht.1]
  exact ⟨hlo.trans hu.1, hu.2.trans hhi⟩

theorem triangle_outer_first :
    Wu08TerminalAlignment.fifthMain =
      4*∫ t in a..b, ∫ y in t..b,
        wuLowerCoefficient ((1/2-t-y)/a)/(t*y*(1/2-t-y)) := by
  have hp := truncatedSixthLower_parameters
  change fifthPairFdelta 0 = _
  rw [fifthPair_literal_integral (by norm_num : (0 : ℝ) ≤ 0) (by norm_num)]
  rw [show (∫ v : ℝ × ℝ, fifthPairKernel 0 v) =
      ∫ t, ∫ y, fifthPairKernel 0 (t,y) from
    integral_prod _ (fifthPair_kernel_integrable (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num))]
  have hs : Function.support (fun t => ∫ y, fifthPairKernel 0 (t,y)) ⊆ Icc a b := by
    intro t ht
    by_contra hn
    apply ht
    change (∫ y, fifthPairKernel 0 (t,y)) = 0
    have hz : (fun y => fifthPairKernel 0 (t,y)) = 0 := by
      funext y
      have hv : (t,y) ∉ fifthPairRegion := fun h => hn ⟨h.1, h.2.1.trans h.2.2⟩
      simp [fifthPairKernel, hv]
    rw [hz]
    simp
  rw [truncatedSixthMass_integral_eq_interval hp.2.1.le hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hp.2.1.le] at ht
  have hs' : Function.support (fun y => fifthPairKernel 0 (t,y)) ⊆ Icc t b := by
    intro y hy
    by_cases hv : (t,y) ∈ fifthPairRegion
    · exact ⟨hv.2.1, hv.2.2⟩
    · exact False.elim (hy (by simp [fifthPairKernel, hv]))
  change (∫ y, fifthPairKernel 0 (t,y)) = _
  rw [truncatedSixthMass_integral_eq_interval ht.2 hs']
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le ht.2] at hy
  simpa only [truncatedSixthLowerS, truncatedSixthLowerC, sub_zero, a] using
    fifthPair_kernel_original (δ := 0) (by norm_num) (by norm_num)
      (v := (t,y)) ⟨ht.1, hy.1, hy.2⟩

theorem paper_inner_substitution (t : ℝ) :
    2*(∫ u in ((1/2-b-t)/a)..((1/2-2*t)/a), paperKernel t u) =
      ∫ y in t..b, wuLowerCoefficient ((1/2-t-y)/a)/(t*y*(1/2-t-y)) := by
  have ha : a ≠ 0 := truncatedSixthLower_parameters.1.ne'
  have h := intervalIntegral.integral_comp_sub_div (paperKernel t) ha ((1/2-t)/a)
    (a := t) (b := b)
  have he1 : (1/2-t)/a-b/a = (1/2-b-t)/a := by ring
  have he2 : (1/2-t)/a-t/a = (1/2-2*t)/a := by ring
  rw [he1, he2, smul_eq_mul] at h
  have hk : (fun y => paperKernel t ((1/2-t)/a-y/a)) =
      fun y => (a/2)*(wuLowerCoefficient ((1/2-t-y)/a)/(t*y*(1/2-t-y))) := by
    funext y
    rw [show (1/2-t)/a-y/a = (1/2-t-y)/a by ring]
    unfold paperKernel
    rw [show 1-2*t-2*a*((1/2-t-y)/a) = 2*y by field_simp [ha]; ring]
    field_simp [ha]
  rw [hk, intervalIntegral.integral_const_mul] at h
  apply mul_left_cancel₀ ha
  linarith only [h]

theorem paper_classical_eq_fifthMain : paperClassical = Wu08TerminalAlignment.fifthMain := by
  rw [triangle_outer_first]
  unfold paperClassical
  have hi : (∫ t in a..b,
      2*(∫ u in ((1/2-b-t)/a)..((1/2-2*t)/a), paperKernel t u)) =
      ∫ t in a..b, ∫ y in t..b,
        wuLowerCoefficient ((1/2-t-y)/a)/(t*y*(1/2-t-y)) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact paper_inner_substitution t
  rw [intervalIntegral.integral_const_mul] at hi
  linarith only [hi]

end
end WuTarget.Wu08FifthSource
