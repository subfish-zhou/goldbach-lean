import MathlibNt.SieveTheory.LiLiuGoldbachS3PrimeKernel

open Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

/-- Exact argument range of the unchanged S3 integrand. -/
theorem goldbachS3_scalar_argument_mem {u : ℝ}
    (hu : u ∈ Icc (4 / 53 : ℝ) (1 / 3 : ℝ)) :
    ((1 / 2 : ℝ) - u) / (4 / 53 : ℝ) ∈ Icc (53 / 24 : ℝ) (45 / 8 : ℝ) := by
  constructor <;> linarith [hu.1, hu.2]

/-- Compact integrability of the literal production kernel, not a surrogate. -/
theorem goldbachS3_scalar_intervalIntegrable {β : ℝ}
    (hβ : (4 / 53 : ℝ) ≤ β) (hβu : β ≤ (1 / 3 : ℝ)) :
    IntervalIntegrable (fun u : ℝ =>
      suzukiContinuousUpperFactor (((1 / 2 : ℝ) - u) / (4 / 53 : ℝ)) / u)
      volume (4 / 53 : ℝ) β := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hβ]
  apply ContinuousOn.div
  · apply goldbach_suzukiUpperFactor_continuousOn_threeHalves_seven.comp
      ((continuous_const.sub continuous_id).div_const (4 / 53 : ℝ)).continuousOn
    intro u hu
    have hr := goldbachS3_scalar_argument_mem ⟨hu.1, hu.2.trans hβu⟩
    change (3 / 2 : ℝ) ≤ ((1 / 2 : ℝ) - u) / (4 / 53 : ℝ) ∧
      ((1 / 2 : ℝ) - u) / (4 / 53 : ℝ) ≤ 7
    constructor <;> linarith [hr.1, hr.2]
  · exact continuousOn_id
  · intro u hu
    change u ≠ 0
    linarith [hu.1]

/-- First branch, with the genuine amplitude cancelled exactly. -/
theorem goldbachS3_scalar_exp_cancel_first {s : ℝ}
    (hs : (3 / 2 : ℝ) ≤ s) (hs3 : s ≤ 3) :
    Real.exp (-Real.eulerMascheroniConstant) * suzukiContinuousUpperFactor s = 2 / s := by
  rw [suzukiContinuousUpperFactorFirstIntervalIdentity_of_sourceContract
    jr1965Section13HatLayers jr1965Section13HatSourceContract s hs hs3,
    suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
      jr1965Section13HatSourceContract]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- Second branch, with no source-contract premise exposed to the consumer. -/
theorem goldbachS3_scalar_exp_cancel_second {s : ℝ} (hs : 3 ≤ s) (hs5 : s ≤ 5) :
    Real.exp (-Real.eulerMascheroniConstant) * suzukiContinuousUpperFactor s =
      2 / s * (1 + jurkatRichertInnerIntegral s) := by
  rw [suzukiContinuousUpperFactor_eq_second_source_formula
    jr1965Section13HatSourceContract hs hs5,
    suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
      jr1965Section13HatSourceContract]
  unfold jurkatRichertInnerIntegral
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- Third branch in exact integrated-lower form, with exp(gamma) cancelled.
The nested integral is retained, including its nonzero correction. -/
theorem goldbachS3_scalar_exp_cancel_third {s : ℝ} (hs : 5 ≤ s) (hs7 : s ≤ 7) :
    Real.exp (-Real.eulerMascheroniConstant) * suzukiContinuousUpperFactor s =
      2 / s * (1 + jurkatRichertInnerIntegral 5 +
        ∫ t in (5 : ℝ)..s,
          (Real.log (t - 2) + ∫ v in (3 : ℝ)..t - 2,
            jurkatRichertInnerIntegral v / v) / (t - 1)) := by
  rw [goldbach_suzukiUpperFactor_eq_third hs hs7]
  unfold goldbachUpperThirdIntervalFactor
  have hp : (fun t : ℝ => dimensionOneLowerLinearSieveFactor (t - 1)) =
      (fun t : ℝ => (2 * Real.exp Real.eulerMascheroniConstant) *
        ((Real.log (t - 2) + ∫ v in (3 : ℝ)..t - 2,
          jurkatRichertInnerIntegral v / v) / (t - 1))) := by
    funext t
    unfold dimensionOneLowerLinearSieveFactor
    rw [show t - 1 - 1 = t - 2 by ring]
    ring
  rw [hp, intervalIntegral.integral_const_mul, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- Affine change of variables for the literal production integral. -/
theorem goldbachS3_scalar_change_variable (β : ℝ) :
    goldbachS3_primeKernelIntegral β =
      ∫ s in ((1 / 2 : ℝ) - β) / (4 / 53 : ℝ)..(45 / 8 : ℝ),
        suzukiContinuousUpperFactor s / ((53 / 8 : ℝ) - s) := by
  let f : ℝ → ℝ := fun s => suzukiContinuousUpperFactor s / ((53 / 8 : ℝ) - s)
  have hp : (fun u : ℝ => suzukiContinuousUpperFactor
      (((1 / 2 : ℝ) - u) / (4 / 53 : ℝ)) / u) =
      (fun u : ℝ => (53 / 4 : ℝ) * f ((53 / 8 : ℝ) - u / (4 / 53 : ℝ))) := by
    funext u
    have hs : ((1 / 2 : ℝ) - u) / (4 / 53 : ℝ) =
        (53 / 8 : ℝ) - u / (4 / 53 : ℝ) := by ring
    rw [hs]
    dsimp [f]
    rw [show (53 / 8 : ℝ) - (53 / 8 - u / (4 / 53)) = (53 / 4 : ℝ) * u by ring]
    simp only [div_mul_eq_div_div]
    ring
  unfold goldbachS3_primeKernelIntegral
  rw [hp, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_div f (by norm_num : (4 / 53 : ℝ) ≠ 0) (53 / 8 : ℝ)]
  norm_num only [smul_eq_mul]
  rw [show (53 / 8 : ℝ) - β / (4 / 53) = ((1 / 2 : ℝ) - β) / (4 / 53) by ring]
  dsimp [f]
  ring

/-- Exact exp-free reduction on the whole admissible beta range.  The third
branch retains the full iterated lower-factor correction. -/
theorem goldbachS3_scalar_exp_free {β : ℝ}
    (hβ : (4 / 53 : ℝ) ≤ β) (hβu : β ≤ (1 / 3 : ℝ)) :
    (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
        goldbachS3_primeKernelIntegral β =
      53 * ∫ s in ((1 / 2 : ℝ) - β) / (4 / 53 : ℝ)..(45 / 8 : ℝ),
        (if s ≤ 3 then 1 else if s ≤ 5 then 1 + jurkatRichertInnerIntegral s else
          1 + jurkatRichertInnerIntegral 5 +
            ∫ t in (5 : ℝ)..s,
              (Real.log (t - 2) + ∫ v in (3 : ℝ)..t - 2,
                jurkatRichertInnerIntegral v / v) / (t - 1)) /
          (s * ((53 / 8 : ℝ) - s)) := by
  rw [goldbachS3_scalar_change_variable, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (show ((1 / 2 : ℝ) - β) / (4 / 53 : ℝ) ≤ (45 / 8 : ℝ)
    by linarith)] at hs
  have hslo : (3 / 2 : ℝ) ≤ s := by linarith [hs.1]
  have hshi : s ≤ 7 := by linarith [hs.2]
  have hs0 : s ≠ 0 := by linarith
  have hden : (53 / 8 : ℝ) - s ≠ 0 := by linarith [hs.2]
  dsimp only
  by_cases hs3 : s ≤ 3
  · rw [if_pos hs3]
    have h := goldbachS3_scalar_exp_cancel_first hslo hs3
    field_simp [hs0, hden] at h ⊢
    rw [h]
  · by_cases hs5 : s ≤ 5
    · rw [if_neg hs3, if_pos hs5]
      have h := goldbachS3_scalar_exp_cancel_second (by linarith) hs5
      field_simp [hs0, hden] at h ⊢
      rw [h]
    · rw [if_neg hs3, if_neg hs5]
      have h := goldbachS3_scalar_exp_cancel_third (by linarith) hshi
      field_simp [hs0, hden] at h ⊢
      rw [h]

/-- All three actual source branches, glued without changing the factor. -/
theorem goldbachS3_scalar_exp_cancel {s : ℝ} (hs : (3 / 2 : ℝ) ≤ s) (hs7 : s ≤ 7) :
    Real.exp (-Real.eulerMascheroniConstant) * suzukiContinuousUpperFactor s =
      2 / s * (if s ≤ 3 then 1 else if s ≤ 5 then 1 + jurkatRichertInnerIntegral s else
        1 + jurkatRichertInnerIntegral 5 +
          ∫ t in (5 : ℝ)..s,
            (Real.log (t - 2) + ∫ v in (3 : ℝ)..t - 2,
              jurkatRichertInnerIntegral v / v) / (t - 1)) := by
  split_ifs with hs3 hs5
  · simpa only [mul_one] using goldbachS3_scalar_exp_cancel_first hs hs3
  · exact goldbachS3_scalar_exp_cancel_second (by linarith) hs5
  · exact goldbachS3_scalar_exp_cancel_third (by linarith) hs7

/-- Genuine continuity of the exp-free expression, including both joins.
Thus the change of variables is not exploiting a nonintegrable zero value. -/
theorem goldbachS3_scalar_exp_free_continuousOn :
    ContinuousOn (fun s : ℝ =>
      (if s ≤ 3 then 1 else if s ≤ 5 then 1 + jurkatRichertInnerIntegral s else
        1 + jurkatRichertInnerIntegral 5 +
          ∫ t in (5 : ℝ)..s,
            (Real.log (t - 2) + ∫ v in (3 : ℝ)..t - 2,
              jurkatRichertInnerIntegral v / v) / (t - 1)) /
        (s * ((53 / 8 : ℝ) - s))) (Icc (53 / 24 : ℝ) (45 / 8 : ℝ)) := by
  have hc : ContinuousOn (fun s : ℝ =>
      Real.exp (-Real.eulerMascheroniConstant) * suzukiContinuousUpperFactor s /
        (2 * ((53 / 8 : ℝ) - s))) (Icc (53 / 24 : ℝ) (45 / 8 : ℝ)) := by
    apply ContinuousOn.div
    · apply continuousOn_const.mul
      exact goldbach_suzukiUpperFactor_continuousOn_threeHalves_seven.mono
        (Icc_subset_Icc (by norm_num) (by norm_num))
    · exact continuousOn_const.mul (continuousOn_const.sub continuousOn_id)
    · intro s hs
      change 2 * ((53 / 8 : ℝ) - s) ≠ 0
      have hh : (53 / 8 : ℝ) - s ≠ 0 := by linarith [hs.2]
      exact mul_ne_zero (by norm_num) hh
  apply hc.congr
  intro s hs
  dsimp only
  rw [goldbachS3_scalar_exp_cancel (by linarith [hs.1]) (by linarith [hs.2])]
  simp only [div_mul_eq_div_div]
  ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig