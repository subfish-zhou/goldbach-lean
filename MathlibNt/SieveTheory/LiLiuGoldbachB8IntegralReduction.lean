import MathlibNt.SieveTheory.LiLiuGoldbachB8LogGridLimit
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory Set
open scoped Interval

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable section

private lemma B8IntegralReduction_u_pos {u : ℝ}
    (hu : u ∈ Icc (3 / 11 : ℝ) (1 / 3)) :
    0 < u ∧ 0 < 1 - u ∧ u ≤ (1 - u) / 2 := by
  constructor
  · linarith [hu.1]
  constructor <;> linarith [hu.2]

private lemma B8IntegralReduction_inner_pos {u v : ℝ}
    (hu : u ∈ Icc (3 / 11 : ℝ) (1 / 3))
    (hv : v ∈ Icc u ((1 - u) / 2)) :
    0 < v ∧ 0 < 1 - u - v := by
  have hp := B8IntegralReduction_u_pos hu
  constructor
  · linarith [hv.1]
  · linarith [hv.2]

/-- Exact inner evaluation, including the degenerate interval at `u = 1/3`. -/
theorem goldbachB8InnerIntegral_eq {u : ℝ}
    (hu : u ∈ Icc (3 / 11 : ℝ) (1 / 3)) :
    (∫ v in u..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
      Real.log ((1 - 2 * u) / u) / (u * (1 - u)) := by
  obtain ⟨hu_pos, hu_one_pos, hle⟩ := B8IntegralReduction_u_pos hu
  have hleft : IntervalIntegrable (fun v : ℝ => v⁻¹) volume u ((1 - u) / 2) := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro v hv
      rw [uIcc_of_le hle] at hv
      exact (B8IntegralReduction_inner_pos hu hv).1.ne'
    · exact continuousOn_id
  have hright : IntervalIntegrable (fun v : ℝ => (1 - u - v)⁻¹) volume
      u ((1 - u) / 2) := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro v hv
      rw [uIcc_of_le hle] at hv
      exact (B8IntegralReduction_inner_pos hu hv).2.ne'
    · exact continuousOn_const.sub continuousOn_id
  have hreflect :
      (∫ v in u..((1 - u) / 2), (1 - u - v)⁻¹) =
        ∫ v in (1 - u) - ((1 - u) / 2)..(1 - u) - u, v⁻¹ := by
    simpa only using
      (intervalIntegral.integral_comp_sub_left (f := fun v : ℝ => v⁻¹)
        (a := u) (b := (1 - u) / 2) (1 - u))
  have hhalf_pos : 0 < (1 - u) / 2 := by positivity
  have htail_pos : 0 < 1 - u - u := by linarith [hu.2]
  have hratio_left_pos : 0 < ((1 - u) / 2) / u := div_pos hhalf_pos hu_pos
  have hratio_right_pos : 0 < (1 - u - u) / ((1 - u) / 2) :=
    div_pos htail_pos hhalf_pos
  have hmul :
      (((1 - u) / 2) / u) * ((1 - u - u) / ((1 - u) / 2)) =
        (1 - 2 * u) / u := by
    field_simp [hu_pos.ne', hhalf_pos.ne']
    ring
  calc
    (∫ v in u..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
        ∫ v in u..((1 - u) / 2),
          (1 / (u * (1 - u))) * (v⁻¹ + (1 - u - v)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hle] at hv
      have hp := B8IntegralReduction_inner_pos hu hv
      field_simp [hu_pos.ne', hu_one_pos.ne', hp.1.ne', hp.2.ne']
      ring
    _ = (1 / (u * (1 - u))) *
        ((∫ v in u..((1 - u) / 2), v⁻¹) +
          ∫ v in u..((1 - u) / 2), (1 - u - v)⁻¹) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hleft hright]
    _ = (1 / (u * (1 - u))) *
        (Real.log (((1 - u) / 2) / u) +
          Real.log ((1 - u - u) / ((1 - u) / 2))) := by
      rw [integral_inv_of_pos hu_pos hhalf_pos, hreflect]
      rw [show (1 - u) - ((1 - u) / 2) = (1 - u) / 2 by ring]
      rw [integral_inv_of_pos hhalf_pos htail_pos]
    _ = (1 / (u * (1 - u))) *
        Real.log ((((1 - u) / 2) / u) * ((1 - u - u) / ((1 - u) / 2))) := by
      rw [← Real.log_mul hratio_left_pos.ne' hratio_right_pos.ne']
    _ = Real.log ((1 - 2 * u) / u) / (u * (1 - u)) := by
      rw [hmul]
      ring

theorem goldbachB8InnerIntegral_eq_reciprocal {u : ℝ}
    (hu : u ∈ Icc (3 / 11 : ℝ) (1 / 3)) :
    (∫ v in u..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
      Real.log (1 / u - 2) / (u * (1 - u)) := by
  rw [goldbachB8InnerIntegral_eq hu]
  have harg : (1 - 2 * u) / u = 1 / u - 2 := by
    field_simp [(B8IntegralReduction_u_pos hu).1.ne']
  rw [harg]

/-- This is the production double integral itself, with no factor eight. -/
theorem goldbachB8MainIntegral_eq_singleIntegral :
    goldbachB8MainIntegral =
      ∫ u in (3 / 11 : ℝ)..(1 / 3), Real.log (1 / u - 2) / (u * (1 - u)) := by
  unfold goldbachB8MainIntegral
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by norm_num : (3 / 11 : ℝ) ≤ 1 / 3)] at hu
  exact goldbachB8InnerIntegral_eq_reciprocal hu

private lemma B8IntegralReduction_log_arg_ge_one {u : ℝ}
    (hu : u ∈ Icc (3 / 11 : ℝ) (1 / 3)) :
    1 ≤ 1 / u - 2 := by
  have hp := (B8IntegralReduction_u_pos hu).1
  have h : (3 : ℝ) ≤ 1 / u := (le_div_iff₀ hp).2 (by linarith [hu.2])
  linarith

theorem continuousOn_goldbachB8SingleIntegrand :
    ContinuousOn (fun u : ℝ => Real.log (1 / u - 2) / (u * (1 - u)))
      (Icc (3 / 11 : ℝ) (1 / 3)) := by
  have hinv : ContinuousOn (fun u : ℝ => 1 / u) (Icc (3 / 11 : ℝ) (1 / 3)) :=
    continuousOn_const.div continuousOn_id
      (fun _ hu => (B8IntegralReduction_u_pos hu).1.ne')
  apply ContinuousOn.div
    ((hinv.sub continuousOn_const).log (fun u hu => by
      change 1 / u - 2 ≠ 0
      have h := B8IntegralReduction_log_arg_ge_one hu
      linarith))
    (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
  intro u hu
  have hp := B8IntegralReduction_u_pos hu
  exact mul_ne_zero hp.1.ne' hp.2.1.ne'

theorem intervalIntegrable_goldbachB8SingleIntegrand :
    IntervalIntegrable (fun u : ℝ => Real.log (1 / u - 2) / (u * (1 - u)))
      volume (3 / 11) (1 / 3) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (3 / 11 : ℝ) ≤ 1 / 3)]
  exact continuousOn_goldbachB8SingleIntegrand

theorem goldbachB8SingleIntegrand_nonneg {u : ℝ}
    (hu : u ∈ Icc (3 / 11 : ℝ) (1 / 3)) :
    0 ≤ Real.log (1 / u - 2) / (u * (1 - u)) := by
  have hp := B8IntegralReduction_u_pos hu
  exact div_nonneg (Real.log_nonneg (B8IntegralReduction_log_arg_ge_one hu))
    (mul_pos hp.1 hp.2.1).le

theorem continuousOn_goldbachB8TransformedIntegrand :
    ContinuousOn (fun t : ℝ => Real.log (t - 1) / t) (Icc (2 : ℝ) (8 / 3)) := by
  apply ContinuousOn.div
    ((continuousOn_id.sub continuousOn_const).log (fun t ht => by
      change t - 1 ≠ 0
      linarith [ht.1]))
    continuousOn_id
  intro t ht
  change t ≠ 0
  linarith [ht.1]

theorem intervalIntegrable_goldbachB8TransformedIntegrand :
    IntervalIntegrable (fun t : ℝ => Real.log (t - 1) / t) volume 2 (8 / 3) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 8 / 3)]
  exact continuousOn_goldbachB8TransformedIntegrand

theorem goldbachB8TransformedIntegrand_nonneg {t : ℝ}
    (ht : t ∈ Icc (2 : ℝ) (8 / 3)) :
    0 ≤ Real.log (t - 1) / t :=
  div_nonneg (Real.log_nonneg (by linarith [ht.1])) (by linarith [ht.1])

theorem goldbachB8ReductionChange_endpoints :
    (1 / ((2 : ℝ) + 1) = 1 / 3) ∧
      (1 / ((8 / 3 : ℝ) + 1) = 3 / 11) := by
  norm_num

theorem goldbachB8ReductionChange_mapsTo :
    MapsTo (fun t : ℝ => 1 / (t + 1)) (Icc (2 : ℝ) (8 / 3))
      (Icc (3 / 11 : ℝ) (1 / 3)) := by
  intro t ht
  have hp : 0 < t + 1 := by linarith [ht.1]
  constructor
  · apply (le_div_iff₀ hp).2
    linarith [ht.2]
  · apply (div_le_iff₀ hp).2
    linarith [ht.1]

theorem hasDerivAt_goldbachB8ReductionChange {t : ℝ}
    (ht : t ∈ Icc (2 : ℝ) (8 / 3)) :
    HasDerivAt (fun t : ℝ => 1 / (t + 1)) (-1 / (t + 1) ^ 2) t := by
  have hp : t + 1 ≠ 0 := by linarith [ht.1]
  simpa only [neg_div, one_div] using
    (hasDerivAt_inv hp).comp_add_const t 1

theorem continuousOn_goldbachB8ReductionChange :
    ContinuousOn (fun t : ℝ => 1 / (t + 1)) (Icc (2 : ℝ) (8 / 3)) :=
  continuousOn_const.div (continuousOn_id.add continuousOn_const)
    (fun t ht => by linarith [ht.1])

theorem continuousOn_goldbachB8ReductionJacobian :
    ContinuousOn (fun t : ℝ => -1 / (t + 1) ^ 2) (Icc (2 : ℝ) (8 / 3)) :=
  continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow 2)
    (fun t ht => pow_ne_zero 2 (by linarith [ht.1]))

/-- The negative sign is the Jacobian, before reversal of the integration limits. -/
theorem goldbachB8ReductionChange_integrand {t : ℝ}
    (ht : t ∈ Icc (2 : ℝ) (8 / 3)) :
    (Real.log (1 / (1 / (t + 1)) - 2) /
        ((1 / (t + 1)) * (1 - 1 / (t + 1)))) * (-1 / (t + 1) ^ 2) =
      -(Real.log (t - 1) / t) := by
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hp : t + 1 ≠ 0 := by linarith [ht.1]
  have harg : 1 / (1 / (t + 1)) - 2 = t - 1 := by
    rw [one_div_one_div]
    ring
  rw [harg]
  field_simp [ht0, hp]
  ring

/-- Directed substitution: `g(2) = 1/3` and `g(8/3) = 3/11`. -/
theorem goldbachB8ReductionChange_oriented :
    (∫ t in (2 : ℝ)..(8 / 3),
      (Real.log (1 / (1 / (t + 1)) - 2) /
        ((1 / (t + 1)) * (1 - 1 / (t + 1)))) * (-1 / (t + 1) ^ 2)) =
      ∫ u in (1 / 3 : ℝ)..(3 / 11), Real.log (1 / u - 2) / (u * (1 - u)) := by
  have hderiv : ∀ t ∈ uIcc (2 : ℝ) (8 / 3),
      HasDerivAt (fun t : ℝ => 1 / (t + 1)) (-1 / (t + 1) ^ 2) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 8 / 3)] at ht
    exact hasDerivAt_goldbachB8ReductionChange ht
  have hjac : ContinuousOn (fun t : ℝ => -1 / (t + 1) ^ 2)
      (uIcc (2 : ℝ) (8 / 3)) := by
    rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 8 / 3)]
    exact continuousOn_goldbachB8ReductionJacobian
  have hcont : ContinuousOn (fun u : ℝ => Real.log (1 / u - 2) / (u * (1 - u)))
      ((fun t : ℝ => 1 / (t + 1)) '' uIcc (2 : ℝ) (8 / 3)) := by
    apply continuousOn_goldbachB8SingleIntegrand.mono
    rintro u ⟨t, ht, rfl⟩
    rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 8 / 3)] at ht
    exact goldbachB8ReductionChange_mapsTo ht
  have h := intervalIntegral.integral_comp_mul_deriv' hderiv hjac hcont
  norm_num only at h
  exact h

/-- Exact reduction of actual `I8`; the reversed limits cancel the negative Jacobian. -/
theorem goldbachB8MainIntegral_eq_transformedIntegral :
    goldbachB8MainIntegral =
      ∫ t in (2 : ℝ)..(8 / 3), Real.log (t - 1) / t := by
  have hneg :
      -(∫ t in (2 : ℝ)..(8 / 3), Real.log (t - 1) / t) =
        -(∫ u in (3 / 11 : ℝ)..(1 / 3), Real.log (1 / u - 2) / (u * (1 - u))) := by
    calc
      _ = ∫ t in (2 : ℝ)..(8 / 3),
          (Real.log (1 / (1 / (t + 1)) - 2) /
            ((1 / (t + 1)) * (1 - 1 / (t + 1)))) * (-1 / (t + 1) ^ 2) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 8 / 3)] at ht
        exact (goldbachB8ReductionChange_integrand ht).symm
      _ = ∫ u in (1 / 3 : ℝ)..(3 / 11),
          Real.log (1 / u - 2) / (u * (1 - u)) := goldbachB8ReductionChange_oriented
      _ = _ := intervalIntegral.integral_symm _ _
  rw [goldbachB8MainIntegral_eq_singleIntegral]
  exact (neg_injective hneg).symm

end

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig