import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachG12IntegralReduction

noncomputable section
open MeasureTheory Set
open scoped Interval
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12SharpQuadrature

/-- The exact single-variable density of the four-variable cross. -/
def density (u : ℝ) : ℝ :=
  (1/(4/33 : ℝ) + (Real.log ((4/33 : ℝ)/u)-1)/u)/u

theorem continuousOn_density : ContinuousOn density (Icc (4/53 : ℝ) (4/33)) := by
  have hn : ∀ u ∈ Icc (4/53 : ℝ) (4/33), u ≠ 0 := by
    intro u hu
    linarith [hu.1]
  unfold density
  exact (continuousOn_const.add (((continuousOn_const.div continuousOn_id hn).log
    (fun u hu => div_ne_zero (by norm_num) (hn u hu))).sub continuousOn_const |>.div
      continuousOn_id hn)).div continuousOn_id hn

theorem integrable_weighted (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4/53 : ℝ) (4/33))) :
    IntervalIntegrable (fun u => h u * density u) volume (4/53) (4/33) :=
  (hh.mul continuousOn_density).intervalIntegrable_of_Icc (by norm_num)

theorem integral_eq_density (h : ℝ → ℝ) :
    goldbachG12PrimeIntegral h = Real.log (9/4 : ℝ) *
      ∫ u in (4/53 : ℝ)..(4/33), h u * density u := by
  rw [goldbachG12PrimeIntegral_eq_single]
  rw [show (3/11 : ℝ)/(4/33) = 9/4 by norm_num]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  dsimp [density]
  ring

theorem sharp_low {u : ℝ} (hu : u < 1/10) :
    G12SharpWeight.weight u = (561990/1000000 : ℝ) * goldbachG11AuthorWeight u := by
  simp only [G12SharpWeight.weight, G12SharpWeight.factor, if_pos hu]

theorem sharp_high {u : ℝ} (hu : 1/10 ≤ u) :
    G12SharpWeight.weight u = (564383/1000000 : ℝ) * goldbachG11AuthorWeight u := by
  simp only [G12SharpWeight.weight, G12SharpWeight.factor, if_neg (not_lt.mpr hu)]

private theorem low_integrable (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc (4/53 : ℝ) (4/33))) :
    IntervalIntegrable (fun u => G12SharpWeight.weight u * g u)
      volume (4/53) (1/10) := by
  have hc : (1/10 : ℝ) ∈ uIcc (4/53 : ℝ) (4/33) := by
    rw [uIcc_of_le (by norm_num : (4/53 : ℝ) ≤ 4/33)]
    constructor <;> norm_num
  have hi := (((continuousOn_goldbachG11AuthorWeight.mul hg).intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (4/53 : ℝ) ≤ 4/33)).mono_set
    (uIcc_subset_uIcc left_mem_uIcc hc)).const_mul (561990/1000000 : ℝ)
  apply (intervalIntegrable_congr_uIoo ?_).mp hi
  intro u hu
  rw [uIoo_of_le (by norm_num : (4/53 : ℝ) ≤ 1/10)] at hu
  dsimp only [Pi.mul_apply]
  rw [sharp_low hu.2]
  ring

private theorem high_integrable (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc (4/53 : ℝ) (4/33))) :
    IntervalIntegrable (fun u => G12SharpWeight.weight u * g u)
      volume (1/10) (4/33) := by
  have hc : (1/10 : ℝ) ∈ uIcc (4/53 : ℝ) (4/33) := by
    rw [uIcc_of_le (by norm_num : (4/53 : ℝ) ≤ 4/33)]
    constructor <;> norm_num
  have hi := (((continuousOn_goldbachG11AuthorWeight.mul hg).intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (4/53 : ℝ) ≤ 4/33)).mono_set
    (uIcc_subset_uIcc hc right_mem_uIcc)).const_mul (564383/1000000 : ℝ)
  apply (intervalIntegrable_congr_uIoo ?_).mp hi
  intro u hu
  rw [uIoo_of_le (by norm_num : (1/10 : ℝ) ≤ 4/33)] at hu
  dsimp only [Pi.mul_apply]
  rw [sharp_high hu.1.le]
  ring


/-- Endpoint removal occurs only inside Lebesgue integrals, never in the prime sum. -/
theorem sharp_integral_split :
    goldbachG12PrimeIntegral G12SharpWeight.weight = Real.log (9/4 : ℝ) *
      ((561990/1000000 : ℝ) * (36/5) *
        (∫ u in (4/53 : ℝ)..(1/10), density u / (1-u)) +
      (564383/1000000 : ℝ) * 8 *
        (∫ u in (1/10 : ℝ)..(4/33), density u)) := by
  rw [integral_eq_density, ← intervalIntegral.integral_add_adjacent_intervals
    (low_integrable density continuousOn_density) (high_integrable density continuousOn_density)]
  congr 1
  congr 1
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    dsimp only
    rw [sharp_low hu.2, goldbachG11AuthorWeight_eq_low hu.2.le]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    dsimp only
    rw [sharp_high hu.1.le, goldbachG11AuthorWeight_eq_high hu.1.le]


end G12SharpQuadrature
