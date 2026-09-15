import MathlibNt.Wu2008DoubleSieve.TruncatedSixthClosureEndpoint

/-!
# Classical zero-range and the full sixth-term rectangle

The discarded part has a positive source coordinate below two, where
the actual canonical lower coefficient vanishes. No initial-segment
formula is substituted on the retained part.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Classical Topology
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem truncatedSixthZeroDelta_coefficient_zero {s : ℝ} (hs : s ≤ 2) :
    wuLowerCoefficient s = 0 := by
  simp only [wuLowerCoefficient, jr1965f_initial hs, mul_zero, zero_div]

theorem truncatedSixthZeroDelta_clip_zero {s : ℝ} (hs : s ≤ 2) :
    wuLowerCoefficient (truncatedSixthMassClip s) = 0 := by
  have hclip : truncatedSixthMassClip s = 2 := by
    exact max_eq_left ((min_le_right _ _).trans hs)
  rw [hclip]
  exact truncatedSixthZeroDelta_coefficient_zero le_rfl

theorem truncatedSixthZeroDelta_rectangle_bounds {x y : ℝ}
    (hx : x ∈ Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta)
    (hy : y ∈ Icc truncatedSixthLowerBeta truncatedSixthLowerSigma) :
    0 < x ∧ 0 < y ∧
      0 < 1 / 2 - x - y ∧
      0 < (1 / 2 - x - y) / truncatedSixthLowerAlpha := by
  have hp := truncatedSixthLower_parameters
  have hgap : 0 < 3 * truncatedSixthLowerAlpha - truncatedSixthLowerBeta := by
    linarith [hp.2.2.2.2]
  have hden : 0 < 1 / 2 - x - y := by
    have hsum := add_le_add hx.2 hy.2
    unfold truncatedSixthLowerSigma at hsum
    linarith
  exact ⟨hp.1.trans_le hx.1, (hp.1.trans hp.2.1).trans_le hy.1,
    hden, div_pos hden hp.1⟩

theorem truncatedSixthZeroDelta_discarded_zero {x y : ℝ}
    (hx : x ∈ Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta)
    (hy : y ∈ Icc truncatedSixthLowerBeta truncatedSixthLowerSigma)
    (hcut : ¬truncatedSixthLowerRegion 0 x y) :
    0 < (1 / 2 - x - y) / truncatedSixthLowerAlpha ∧
      (1 / 2 - x - y) / truncatedSixthLowerAlpha < 2 ∧
      wuLowerCoefficient ((1 / 2 - x - y) / truncatedSixthLowerAlpha) = 0 := by
  have hsum : ¬ x + y ≤ truncatedSixthLowerC 0 - 2 * truncatedSixthLowerAlpha :=
    fun h => hcut ⟨hx.1, hx.2, hy.1, hy.2, h⟩
  have hs : (1 / 2 - x - y) / truncatedSixthLowerAlpha < 2 := by
    apply (div_lt_iff₀ truncatedSixthLower_parameters.1).mpr
    simp only [truncatedSixthLowerC, sub_zero] at hsum
    linarith [lt_of_not_ge hsum]
  exact ⟨(truncatedSixthZeroDelta_rectangle_bounds hx hy).2.2.2, hs,
    truncatedSixthZeroDelta_coefficient_zero hs.le⟩

theorem truncatedSixthZeroDelta_full_rectangle :
    truncatedSixthLowerF6lin =
      4 * ∫ x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
        ∫ y in truncatedSixthLowerBeta..truncatedSixthLowerSigma,
          wuLowerCoefficient ((1 / 2 - x - y) / truncatedSixthLowerAlpha) /
            (x * y * (1 / 2 - x - y)) := by
  unfold truncatedSixthLowerF6lin truncatedSixthLowerFdelta
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hx
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le truncatedSixthLower_parameters.2.2.1.le] at hy
  by_cases h : truncatedSixthLowerRegion 0 x y
  · simp only [if_pos h, truncatedSixthLowerS, truncatedSixthLowerC, sub_zero]
  · simp only [if_neg h, (truncatedSixthZeroDelta_discarded_zero hx hy h).2.2, zero_div]

noncomputable def truncatedSixthZeroDeltaRegular (δ : ℝ) (v : ℝ × ℝ) : ℝ :=
  wuLowerCoefficient (truncatedSixthMassClip (truncatedSixthLowerS δ v.1 v.2)) /
    truncatedSixthMassDenominator δ v

theorem truncatedSixthZeroDelta_regular_eq {δ x y : ℝ}
    (hδ : 0 ≤ δ)
    (hx : x ∈ Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta)
    (hy : y ∈ Icc truncatedSixthLowerBeta truncatedSixthLowerSigma) :
    truncatedSixthZeroDeltaRegular δ (x, y) =
      if truncatedSixthLowerRegion δ x y then
        wuLowerCoefficient (truncatedSixthLowerS δ x y) /
          (x * y * (truncatedSixthLowerC δ - x - y)) else 0 := by
  by_cases hr : truncatedSixthLowerRegion δ x y
  · simp only [truncatedSixthZeroDeltaRegular, if_pos hr,
      truncatedSixthMass_clip_eq (truncatedSixthLower_region_bounds hδ hr).2.2.2,
      truncatedSixthMass_denominator_eq (v := (x, y)) hδ hr]
  · have hsum : ¬ x + y ≤ truncatedSixthLowerC δ - 2 * truncatedSixthLowerAlpha :=
      fun h => hr ⟨hx.1, hx.2, hy.1, hy.2, h⟩
    have hs : truncatedSixthLowerS δ x y ≤ 2 := by
      apply (div_le_iff₀ truncatedSixthLower_parameters.1).mpr
      linarith [lt_of_not_ge hsum]
    simp only [truncatedSixthZeroDeltaRegular, truncatedSixthZeroDelta_clip_zero hs, zero_div, if_neg hr]

theorem truncatedSixthZeroDelta_regular_continuous :
    Continuous (fun p : ℝ × (ℝ × ℝ) => truncatedSixthZeroDeltaRegular p.1 p.2) := by
  have hs : Continuous (fun p : ℝ × (ℝ × ℝ) => truncatedSixthLowerS p.1 p.2.1 p.2.2) := by
    unfold truncatedSixthLowerS truncatedSixthLowerC
    fun_prop
  have hd : Continuous (fun p : ℝ × (ℝ × ℝ) => truncatedSixthMassDenominator p.1 p.2) := by
    unfold truncatedSixthMassDenominator truncatedSixthLowerC
    fun_prop
  exact (truncatedSixthMass_clipped_classical_continuous.comp hs).div hd
    (fun p => (truncatedSixthMass_denominator_pos p.1 p.2).ne')

noncomputable def truncatedSixthZeroDeltaExtension (δ : ℝ) : ℝ :=
  4 * ∫ x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
    ∫ y in truncatedSixthLowerBeta..truncatedSixthLowerSigma,
      truncatedSixthZeroDeltaRegular δ (x, y)

theorem truncatedSixthZeroDelta_extension_eq {δ : ℝ} (hδ : 0 ≤ δ) :
    truncatedSixthZeroDeltaExtension δ = truncatedSixthLowerFdelta δ := by
  unfold truncatedSixthZeroDeltaExtension truncatedSixthLowerFdelta
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hx
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le truncatedSixthLower_parameters.2.2.1.le] at hy
  exact truncatedSixthZeroDelta_regular_eq hδ hx hy

end Wu2008DoubleSieve
