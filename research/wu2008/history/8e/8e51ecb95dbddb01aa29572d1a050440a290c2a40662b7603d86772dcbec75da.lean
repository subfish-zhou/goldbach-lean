import R2OmegaHighPaper

noncomputable section
namespace WuPaper.R2OmegaHigh
open Wu2008DoubleSieve WuSource.SrcSingle
open Finset Real Filter Set MeasureTheory
open scoped Classical Topology Interval BigOperators

def regularOuter (j : Fin 4) (δ : ℝ) : ℝ :=
  ∫ t in psiLeft (index j)..psiRight (index j), HighSixDeltaLimit.regularPrimeKernel δ t

theorem regular_outer_eq (j : Fin 4) {δ : ℝ} (hh : δ ≤ 1 / 100) :
    regularOuter j δ = outerIntegral j δ := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (geometry j).2.2.2.2.2.2.2.1] at ht
  have hleft : (1 / 10 : ℝ) ≤ t := (window_endpoints j).1.trans ht.1
  have hright := ht.2.trans (geometry j).2.2.2.2.2.2.2.2.1
  have hgap : (1 / 10 : ℝ) ≤ 1 / 2 - δ - t := by linarith
  simp only [HighSixDeltaLimit.regularPrimeKernel, max_eq_right hleft, max_eq_right hgap]

theorem regular_outer_continuous (j : Fin 4) : Continuous (regularOuter j) :=
  gamma5Gain_moving_integral HighSixDeltaLimit.regularPrimeKernel_continuous
    continuous_const continuous_const

theorem outer_continuousAt_zero (j : Fin 4) : ContinuousAt (outerIntegral j) 0 := by
  have h := (regular_outer_continuous j).continuousAt.tendsto (x := (0 : ℝ))
  rw [regular_outer_eq j (by norm_num)] at h
  apply h.congr'
  filter_upwards [gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100)] with δ hδ
  exact regular_outer_eq j hδ.le

theorem fixed_continuousAt_zero (j : Fin 4) : ContinuousAt (fixedCoefficient j) 0 := by
  have hc : ContinuousAt
      (fun δ => firstFunctionalGainPsi δ (psiNode (index j)) (psiTop (index j))) 0 := by
    unfold firstFunctionalGainPsi
    fun_prop
  exact (continuousAt_const.mul (continuousAt_const.sub hc)).mul (outer_continuousAt_zero j)

theorem coefficient_close (j : Fin 4) {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      |fixedCoefficient j δ - paperCoefficient j| < ε := by
  obtain ⟨r, hr, hb⟩ := Metric.continuousAt_iff.mp (fixed_continuousAt_zero j) ε heps
  refine ⟨min r (1 / 100), lt_min hr (by norm_num), min_le_right _ _, ?_⟩
  intro δ hd hdr
  have h := hb (show dist δ (0 : ℝ) < r by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hd] using
      hdr.trans_le (min_le_left r (1 / 100)))
  simpa only [Real.dist_eq, fixed_zero_eq_paper] using h

theorem common_coefficient_radius {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ < r → ∀ j : Fin 4,
      |fixedCoefficient j δ - paperCoefficient j| < ε := by
  obtain ⟨a, ha, ha1, h0⟩ := coefficient_close 0 heps
  obtain ⟨b, hb, _, h1⟩ := coefficient_close 1 heps
  obtain ⟨c, hc, _, h2⟩ := coefficient_close 2 heps
  obtain ⟨d, hd, _, h3⟩ := coefficient_close 3 heps
  let r := min a (min b (min c d))
  have hra : r ≤ a := min_le_left _ _
  have hrb : r ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hrc : r ≤ c := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrd : r ≤ d := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨r, lt_min ha (lt_min hb (lt_min hc hd)), hra.trans ha1, ?_⟩
  intro δ hδ hδr j
  fin_cases j
  · exact h0 δ hδ (hδr.trans_le hra)
  · exact h1 δ hδ (hδr.trans_le hrb)
  · exact h2 δ hδ (hδr.trans_le hrc)
  · exact h3 δ hδ (hδr.trans_le hrd)

theorem original_four_windows {ε : ℝ} (heps : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 100 ∧ δ ≤ Wu04FirstPaid.commonRadius ∧
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 4,
        psiCount (index j) N ≤ sevenRawSource N δ (index j) ∧
        sevenRawSource N δ (index j) ≤
          (paperCoefficient j + ε) * truncatedSixthMassScale N := by
  obtain ⟨r, hr, hr1, hc⟩ := common_coefficient_radius (half_pos heps)
  let δ := min r Wu04FirstPaid.commonRadius / 2
  have hmin : 0 < min r Wu04FirstPaid.commonRadius := lt_min hr Wu04FirstPaid.commonRadius_pos
  have hd : 0 < δ := half_pos hmin
  have hdr : δ < r := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hh : δ ≤ 1 / 100 := hdr.le.trans hr1
  have hdnum : δ ≤ Wu04FirstPaid.commonRadius :=
    (half_le_self hmin.le).trans (min_le_right _ _)
  obtain ⟨T0, hT04, h0⟩ := raw_fixed_integral_upper 0 hd hh (half_pos heps)
  obtain ⟨T1, _, h1⟩ := raw_fixed_integral_upper 1 hd hh (half_pos heps)
  obtain ⟨T2, _, h2⟩ := raw_fixed_integral_upper 2 hd hh (half_pos heps)
  obtain ⟨T3, _, h3⟩ := raw_fixed_integral_upper 3 hd hh (half_pos heps)
  refine ⟨δ, hd, hh, hdnum, max T0 (max T1 (max T2 T3)), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven j
  have hN2 : 2 ≤ N := by omega
  have hf : sevenRawSource N δ (index j) ≤
      (fixedCoefficient j δ + ε / 2) * truncatedSixthMassScale N := by
    fin_cases j
    · exact h0 N (by omega) hEven
    · exact h1 N (by omega) hEven
    · exact h2 N (by omega) hEven
    · exact h3 N (by omega) hEven
  refine ⟨seven_raw_source_count hN2 hd hh (index j), hf.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (scale_nonneg hN2)
  have h := (abs_lt.mp (hc δ hd hdr j)).2
  linarith only [h]

#check @WuPaper.R2OmegaHigh.regularOuter
#check @WuPaper.R2OmegaHigh.regular_outer_eq
#check @WuPaper.R2OmegaHigh.regular_outer_continuous
#check @WuPaper.R2OmegaHigh.outer_continuousAt_zero
#check @WuPaper.R2OmegaHigh.fixed_continuousAt_zero
#check @WuPaper.R2OmegaHigh.coefficient_close
#check @WuPaper.R2OmegaHigh.common_coefficient_radius
#check @WuPaper.R2OmegaHigh.original_four_windows
#print axioms WuPaper.R2OmegaHigh.regularOuter
#print axioms WuPaper.R2OmegaHigh.regular_outer_eq
#print axioms WuPaper.R2OmegaHigh.regular_outer_continuous
#print axioms WuPaper.R2OmegaHigh.outer_continuousAt_zero
#print axioms WuPaper.R2OmegaHigh.fixed_continuousAt_zero
#print axioms WuPaper.R2OmegaHigh.coefficient_close
#print axioms WuPaper.R2OmegaHigh.common_coefficient_radius
#print axioms WuPaper.R2OmegaHigh.original_four_windows
end WuPaper.R2OmegaHigh
