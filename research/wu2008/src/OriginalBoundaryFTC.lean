import OriginalBoundaryLimit
import MathlibNt.SieveTheory.LiLiuFouvryG9MainScalar
noncomputable section
open MeasureTheory Set Filter
open scoped Interval Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace OriginalU8.Weighted
private theorem inner_domain_pos {u v : ℝ}
    (hu : u ∈ Ioc (0 : ℝ) (1/3)) (hv : v ∈ Icc (1/3 : ℝ) ((1-u)/2)) :
    0 < v ∧ 0 < 1-u-v := by
  constructor <;> linarith [hu.2, hv.1, hv.2]

theorem inner_eq {u : ℝ}
    (hu : u ∈ Ioc (0 : ℝ) (1 / 3 : ℝ)) :
    (∫ v in (1 / 3 : ℝ)..((1 - u) / 2),
      1 / (u * v * (1 - u - v))) =
      Real.log ((1 - u - (1 / 3 : ℝ)) / (1 / 3 : ℝ)) /
        (u * (1 - u)) := by
  have hle : (1 / 3 : ℝ) ≤ (1 - u) / 2 :=
    by linarith [hu.2]
  have hu_pos : 0 < u := by
    exact hu.1
  have hu_one_pos : 0 < 1 - u := by
    linarith [hu.2]
  have hleft : IntervalIntegrable (fun v : ℝ => v⁻¹) volume
      (1 / 3 : ℝ) ((1 - u) / 2) := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro v hv
      rw [uIcc_of_le hle] at hv
      exact (inner_domain_pos hu hv).1.ne'
    · exact continuousOn_id
  have hright : IntervalIntegrable (fun v : ℝ => (1 - u - v)⁻¹) volume
      (1 / 3 : ℝ) ((1 - u) / 2) := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro v hv
      rw [uIcc_of_le hle] at hv
      exact (inner_domain_pos hu hv).2.ne'
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
    exact div_pos hhalf_pos (by norm_num : (0 : ℝ) < 1/3)
  have hratio_right_pos :
      0 < (1 - u - (1 / 3 : ℝ)) / ((1 - u) / 2) := by
    exact div_pos htail_pos hhalf_pos
  have hmul :
      (((1 - u) / 2) / (1 / 3 : ℝ)) *
          ((1 - u - (1 / 3 : ℝ)) / ((1 - u) / 2)) =
        (1 - u - (1 / 3 : ℝ)) / (1 / 3 : ℝ) := by
    field_simp [(by norm_num : (0 : ℝ) < 1/3).ne', hhalf_pos.ne']
  calc
    (∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
        ∫ v in (1 / 3 : ℝ)..((1 - u) / 2),
          (1 / (u * (1 - u))) * (v⁻¹ + (1 - u - v)⁻¹) := by
            apply intervalIntegral.integral_congr
            intro v hv
            rw [uIcc_of_le hle] at hv
            have hpos := inner_domain_pos hu hv
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
            rw [integral_inv_of_pos (by norm_num : (0 : ℝ) < 1/3) hhalf_pos]
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

theorem inner_eq_log {u : ℝ}
    (hu : u ∈ Ioc (0 : ℝ) (1 / 3)) :
    (∫ v in (1 / 3 : ℝ)..((1 - u) / 2), 1 / (u * v * (1 - u - v))) =
      Real.log (2 - 3 * u) / (u * (1 - u)) := by
  rw [inner_eq hu]
  congr 2
  ring

theorem inner_weighted_eq {u : ℝ}
    (hu : u ∈ Ioc (0 : ℝ) (1 / 3)) :
    (∫ v in (1 / 3 : ℝ)..((1 - u) / 2),
      1 / (u * v * (1 - u - v) * (1 - u))) =
      Real.log (2 - 3 * u) / (u * (1 - u)^2) := by
  have heq (v : ℝ) : 1 / (u * v * (1 - u - v) * (1 - u)) =
      (1 / (u * v * (1 - u - v))) * (1 / (1 - u)) := by
    simp only [one_div, mul_inv]
  simp_rw [heq]
  rw [intervalIntegral.integral_mul_const, inner_eq_log hu]
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have hu1 : 1 - u ≠ 0 := by linarith [hu.2]
  field_simp [hu0, hu1]


theorem low_eq_single {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/10) :
    low a = ∫ u in a..(1/10 : ℝ), Real.log (2-3*u)/(u*(1-u)^2) := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hab] at hu
  exact inner_weighted_eq ⟨ha.trans_le hu.1, by linarith [hu.2]⟩

theorem original_low_eq_single :
    low (100/1327) = ∫ u in (100/1327 : ℝ)..(1/10),
      Real.log (2-3*u)/(u*(1-u)^2) := low_eq_single (by norm_num) (by norm_num)


end OriginalU8.Weighted
