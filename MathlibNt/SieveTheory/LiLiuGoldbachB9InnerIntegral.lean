import MathlibNt.SieveTheory.LiLiuGoldbachB10IntegralReduction

open MeasureTheory Set
open scoped Interval
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

private lemma B9InnerReduction_beta_pos : 0 < (4 / 53 : ℝ) := by
  norm_num

private lemma B9InnerReduction_gamma_pos : 0 < (1 / 3 : ℝ) := by
  norm_num

private lemma B9InnerReduction_beta_le_gamma :
    (4 / 53 : ℝ) ≤ (1 / 3 : ℝ) := by
  norm_num

private lemma B9InnerReduction_gamma_lt_one : (1 / 3 : ℝ) < 1 := by
  norm_num

private lemma B9InnerReduction_gamma_le_upper {u : ℝ}
    (hu : u ∈ Icc (4 / 53 : ℝ) (1 / 3 : ℝ)) :
    (1 / 3 : ℝ) ≤ (1 - u) / 2 := by
  have huγ : u ≤ (1 / 3 : ℝ) := by
    exact hu.2
  linarith

private lemma B9InnerReduction_inner_domain_pos {u v : ℝ}
    (hu : u ∈ Icc (4 / 53 : ℝ) (1 / 3 : ℝ))
    (hv : v ∈ Icc (1 / 3 : ℝ) ((1 - u) / 2)) :
    0 < v ∧ 0 < 1 - u - v := by
  constructor
  · linarith [B9InnerReduction_gamma_pos, hv.1]
  · linarith [hu.2, B9InnerReduction_gamma_lt_one, hv.2]

/-- Exact evaluation of the inner `v`-integral in the actual B9 kernel over the
actual closed `u`-interval `[4/53, 1/3]`. -/
theorem goldbachB9InnerIntegral_eq {u : ℝ}
    (hu : u ∈ Icc (4 / 53 : ℝ) (1 / 3 : ℝ)) :
    (∫ v in (1 / 3 : ℝ)..((1 - u) / 2),
      1 / (u * v * (1 - u - v))) =
      Real.log ((1 - u - (1 / 3 : ℝ)) / (1 / 3 : ℝ)) /
        (u * (1 - u)) := by
  have hle : (1 / 3 : ℝ) ≤ (1 - u) / 2 :=
    B9InnerReduction_gamma_le_upper hu
  have hu_pos : 0 < u := by
    linarith [hu.1, B9InnerReduction_beta_pos]
  have hu_one_pos : 0 < 1 - u := by
    linarith [hu.2, B9InnerReduction_gamma_lt_one]
  have hleft : IntervalIntegrable (fun v : ℝ => v⁻¹) volume
      (1 / 3 : ℝ) ((1 - u) / 2) := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro v hv
      rw [uIcc_of_le hle] at hv
      exact (B9InnerReduction_inner_domain_pos hu hv).1.ne'
    · exact continuousOn_id
  have hright : IntervalIntegrable (fun v : ℝ => (1 - u - v)⁻¹) volume
      (1 / 3 : ℝ) ((1 - u) / 2) := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro v hv
      rw [uIcc_of_le hle] at hv
      exact (B9InnerReduction_inner_domain_pos hu hv).2.ne'
    · exact continuousOn_const.sub continuousOn_id
  have hreflect :
      (∫ v in (1 / 3 : ℝ)..((1 - u) / 2), (1 - u - v)⁻¹) =
        ∫ v in (1 - u) - ((1 - u) / 2)..(1 - u) - (1 / 3 : ℝ), v⁻¹ := by
    simpa only using
      (intervalIntegral.integral_comp_sub_left
        (f := fun v : ℝ => v⁻¹) (a := (1 / 3 : ℝ))
        (b := (1 - u) / 2) (1 - u))
  have hhalf_pos : 0 < (1 - u) / 2 := by
    positivity
  have htail_pos : 0 < 1 - u - (1 / 3 : ℝ) := by
    linarith [hu.2]
  have hratio_left_pos : 0 < ((1 - u) / 2) / (1 / 3 : ℝ) := by
    exact div_pos hhalf_pos B9InnerReduction_gamma_pos
  have hratio_right_pos :
      0 < (1 - u - (1 / 3 : ℝ)) / ((1 - u) / 2) := by
    exact div_pos htail_pos hhalf_pos
  have hmul :
      (((1 - u) / 2) / (1 / 3 : ℝ)) *
          ((1 - u - (1 / 3 : ℝ)) / ((1 - u) / 2)) =
        (1 - u - (1 / 3 : ℝ)) / (1 / 3 : ℝ) := by
    field_simp [B9InnerReduction_gamma_pos.ne', hhalf_pos.ne']
  calc
    (∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
        ∫ v in (1 / 3 : ℝ)..((1 - u) / 2),
          (1 / (u * (1 - u))) * (v⁻¹ + (1 - u - v)⁻¹) := by
            apply intervalIntegral.integral_congr
            intro v hv
            rw [uIcc_of_le hle] at hv
            have hpos := B9InnerReduction_inner_domain_pos hu hv
            field_simp [hu_pos.ne', hu_one_pos.ne', hpos.1.ne', hpos.2.ne']
            ring
    _ = (1 / (u * (1 - u))) *
        (∫ v in (1 / 3 : ℝ)..((1 - u) / 2),
          (v⁻¹ + (1 - u - v)⁻¹)) := by
            rw [intervalIntegral.integral_const_mul]
    _ = (1 / (u * (1 - u))) *
        ((∫ v in (1 / 3 : ℝ)..((1 - u) / 2), v⁻¹) +
          ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), (1 - u - v)⁻¹) := by
            rw [intervalIntegral.integral_add hleft hright]
    _ = (1 / (u * (1 - u))) *
        (Real.log (((1 - u) / 2) / (1 / 3 : ℝ)) +
          Real.log ((1 - u - (1 / 3 : ℝ)) / ((1 - u) / 2))) := by
            rw [integral_inv_of_pos B9InnerReduction_gamma_pos hhalf_pos]
            rw [hreflect]
            rw [show (1 - u) - ((1 - u) / 2) = (1 - u) / 2 by ring]
            rw [integral_inv_of_pos hhalf_pos htail_pos]
    _ = (1 / (u * (1 - u))) *
        Real.log
          ((((1 - u) / 2) / (1 / 3 : ℝ)) *
            ((1 - u - (1 / 3 : ℝ)) / ((1 - u) / 2))) := by
            rw [← Real.log_mul hratio_left_pos.ne' hratio_right_pos.ne']
    _ = (1 / (u * (1 - u))) *
        Real.log ((1 - u - (1 / 3 : ℝ)) / (1 / 3 : ℝ)) := by
            rw [hmul]
    _ = Real.log ((1 - u - (1 / 3 : ℝ)) / (1 / 3 : ℝ)) /
        (u * (1 - u)) := by
            simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

theorem goldbachB9InnerIntegral_eq_logTwoSubThree {u : ℝ}
    (hu : u ∈ Icc (4 / 53 : ℝ) (1 / 3)) :
    (∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
      Real.log (2 - 3 * u) / (u * (1 - u)) := by
  rw [goldbachB9InnerIntegral_eq hu]
  congr 2
  ring

theorem goldbachB9DoubleIntegral_eq_singleIntegral :
    (∫ u in (4 / 53 : ℝ)..(1 / 3),
      ∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
      ∫ u in (4 / 53 : ℝ)..(1 / 3), Real.log (2 - 3 * u) / (u * (1 - u)) := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le B9InnerReduction_beta_le_gamma] at hu
  exact goldbachB9InnerIntegral_eq_logTwoSubThree hu

theorem continuousOn_goldbachB9SingleIntegrand :
    ContinuousOn (fun u : ℝ => Real.log (2 - 3 * u) / (u * (1 - u)))
      (Icc (4 / 53 : ℝ) (1 / 3)) := by
  apply ContinuousOn.div
    ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).log
      (fun u hu => by change 2 - 3 * u ≠ 0; linarith [hu.2]))
    (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
  intro u hu
  exact mul_ne_zero (by change u ≠ 0; linarith [hu.1])
    (by change 1 - u ≠ 0; linarith [hu.2])

theorem intervalIntegrable_goldbachB9SingleIntegrand :
    IntervalIntegrable (fun u : ℝ => Real.log (2 - 3 * u) / (u * (1 - u)))
      volume (4 / 53) (1 / 3) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le B9InnerReduction_beta_le_gamma]
  exact continuousOn_goldbachB9SingleIntegrand

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig