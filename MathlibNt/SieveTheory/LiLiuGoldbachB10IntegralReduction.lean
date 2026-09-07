import MathlibNt.SieveTheory.LiLiuGoldbachB10LogGridLimit
import MathlibNt.SieveTheory.LiLiuGoldbachB10LogMass
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Filter MeasureTheory Set
open scoped Interval

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable section

private lemma B10IntegralReduction_beta_pos : 0 < goldbachB10Beta := by
  dsimp [goldbachB10Beta]
  norm_num

private lemma B10IntegralReduction_gamma_pos : 0 < goldbachB10Gamma := by
  dsimp [goldbachB10Gamma]
  norm_num

private lemma B10IntegralReduction_beta_le_gamma :
    goldbachB10Beta ≤ goldbachB10Gamma := by
  dsimp [goldbachB10Beta, goldbachB10Gamma]
  norm_num

private lemma B10IntegralReduction_gamma_lt_one : goldbachB10Gamma < 1 := by
  dsimp [goldbachB10Gamma]
  norm_num

private lemma B10IntegralReduction_gamma_le_upper {u : ℝ}
    (hu : u ∈ Icc goldbachB10Beta goldbachB10Gamma) :
    goldbachB10Gamma ≤ (1 - u) / 2 := by
  have huγ : u ≤ (3 / 11 : ℝ) := by
    simpa [goldbachB10Gamma] using hu.2
  dsimp [goldbachB10Gamma]
  linarith

private lemma B10IntegralReduction_inner_domain_pos {u v : ℝ}
    (hu : u ∈ Icc goldbachB10Beta goldbachB10Gamma)
    (hv : v ∈ Icc goldbachB10Gamma ((1 - u) / 2)) :
    0 < v ∧ 0 < 1 - u - v := by
  constructor
  · linarith [B10IntegralReduction_gamma_pos, hv.1]
  · linarith [hu.2, B10IntegralReduction_gamma_lt_one, hv.2]

/-- Exact evaluation of the inner `v`-integral in Liu's printed `I10` over the
actual closed `u`-interval `[β, γ]`. -/
theorem goldbachB10InnerIntegral_eq {u : ℝ}
    (hu : u ∈ Icc goldbachB10Beta goldbachB10Gamma) :
    (∫ v in goldbachB10Gamma..((1 - u) / 2),
      1 / (u * v * (1 - u - v))) =
      Real.log ((1 - u - goldbachB10Gamma) / goldbachB10Gamma) /
        (u * (1 - u)) := by
  have hle : goldbachB10Gamma ≤ (1 - u) / 2 :=
    B10IntegralReduction_gamma_le_upper hu
  have hu_pos : 0 < u := by
    linarith [hu.1, B10IntegralReduction_beta_pos]
  have hu_one_pos : 0 < 1 - u := by
    linarith [hu.2, B10IntegralReduction_gamma_lt_one]
  have hleft : IntervalIntegrable (fun v : ℝ => v⁻¹) volume
      goldbachB10Gamma ((1 - u) / 2) := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro v hv
      rw [uIcc_of_le hle] at hv
      exact (B10IntegralReduction_inner_domain_pos hu hv).1.ne'
    · exact continuousOn_id
  have hright : IntervalIntegrable (fun v : ℝ => (1 - u - v)⁻¹) volume
      goldbachB10Gamma ((1 - u) / 2) := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro v hv
      rw [uIcc_of_le hle] at hv
      exact (B10IntegralReduction_inner_domain_pos hu hv).2.ne'
    · exact continuousOn_const.sub continuousOn_id
  have hreflect :
      (∫ v in goldbachB10Gamma..((1 - u) / 2), (1 - u - v)⁻¹) =
        ∫ v in (1 - u) - ((1 - u) / 2)..(1 - u) - goldbachB10Gamma, v⁻¹ := by
    simpa only using
      (intervalIntegral.integral_comp_sub_left
        (f := fun v : ℝ => v⁻¹) (a := goldbachB10Gamma)
        (b := (1 - u) / 2) (1 - u))
  have hhalf_pos : 0 < (1 - u) / 2 := by
    positivity
  have htail_pos : 0 < 1 - u - goldbachB10Gamma := by
    linarith [hu.2]
  have hratio_left_pos : 0 < ((1 - u) / 2) / goldbachB10Gamma := by
    exact div_pos hhalf_pos B10IntegralReduction_gamma_pos
  have hratio_right_pos :
      0 < (1 - u - goldbachB10Gamma) / ((1 - u) / 2) := by
    exact div_pos htail_pos hhalf_pos
  have hmul :
      (((1 - u) / 2) / goldbachB10Gamma) *
          ((1 - u - goldbachB10Gamma) / ((1 - u) / 2)) =
        (1 - u - goldbachB10Gamma) / goldbachB10Gamma := by
    field_simp [B10IntegralReduction_gamma_pos.ne', hhalf_pos.ne']
  calc
    (∫ v in goldbachB10Gamma..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
        ∫ v in goldbachB10Gamma..((1 - u) / 2),
          (1 / (u * (1 - u))) * (v⁻¹ + (1 - u - v)⁻¹) := by
            apply intervalIntegral.integral_congr
            intro v hv
            rw [uIcc_of_le hle] at hv
            have hpos := B10IntegralReduction_inner_domain_pos hu hv
            field_simp [hu_pos.ne', hu_one_pos.ne', hpos.1.ne', hpos.2.ne']
            ring
    _ = (1 / (u * (1 - u))) *
        (∫ v in goldbachB10Gamma..((1 - u) / 2),
          (v⁻¹ + (1 - u - v)⁻¹)) := by
            rw [intervalIntegral.integral_const_mul]
    _ = (1 / (u * (1 - u))) *
        ((∫ v in goldbachB10Gamma..((1 - u) / 2), v⁻¹) +
          ∫ v in goldbachB10Gamma..((1 - u) / 2), (1 - u - v)⁻¹) := by
            rw [intervalIntegral.integral_add hleft hright]
    _ = (1 / (u * (1 - u))) *
        (Real.log (((1 - u) / 2) / goldbachB10Gamma) +
          Real.log ((1 - u - goldbachB10Gamma) / ((1 - u) / 2))) := by
            rw [integral_inv_of_pos B10IntegralReduction_gamma_pos hhalf_pos]
            rw [hreflect]
            rw [show (1 - u) - ((1 - u) / 2) = (1 - u) / 2 by ring]
            rw [integral_inv_of_pos hhalf_pos htail_pos]
    _ = (1 / (u * (1 - u))) *
        Real.log
          ((((1 - u) / 2) / goldbachB10Gamma) *
            ((1 - u - goldbachB10Gamma) / ((1 - u) / 2))) := by
            rw [← Real.log_mul hratio_left_pos.ne' hratio_right_pos.ne']
    _ = (1 / (u * (1 - u))) *
        Real.log ((1 - u - goldbachB10Gamma) / goldbachB10Gamma) := by
            rw [hmul]
    _ = Real.log ((1 - u - goldbachB10Gamma) / goldbachB10Gamma) /
        (u * (1 - u)) := by
            simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- Liu's exact double integral `goldbachB10MainIntegral` reduces to a single
closed-form interval integral. -/
theorem goldbachB10MainIntegral_eq_singleIntegral :
    goldbachB10MainIntegral =
      ∫ u in goldbachB10Beta..goldbachB10Gamma,
        Real.log ((1 - u - goldbachB10Gamma) / goldbachB10Gamma) /
          (u * (1 - u)) := by
  unfold goldbachB10MainIntegral
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le B10IntegralReduction_beta_le_gamma] at hu
  exact goldbachB10InnerIntegral_eq hu

/-- The production alias `goldbachB10I10` is exactly the reduced
one-dimensional integral. -/
theorem goldbachB10I10_eq_singleIntegral :
    goldbachB10I10 =
      ∫ u in goldbachB10Beta..goldbachB10Gamma,
        Real.log ((1 - u - goldbachB10Gamma) / goldbachB10Gamma) /
          (u * (1 - u)) := by
  rw [show goldbachB10I10 = goldbachB10MainIntegral by rfl]
  exact goldbachB10MainIntegral_eq_singleIntegral

end

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig