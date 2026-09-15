import WR2SixthCountCarriers
import WRMapMSixthClassical

noncomputable section
namespace WuPaper.R2SixthCount
open Real Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6High Wu2008DoubleSieve
open scoped Interval

theorem c_classical_kernel_zero {x y : ℝ}
    (hx : x ∈ Icc bCut WuPaper.R2SixthCount.beta)
    (hy : y ∈ Icc aCeiling sigma) :
    kernel wuLowerCoefficient x y = 0 := by
  have hs := c_classical_parameter hx hy
  unfold kernel u
  rw [truncatedSixthZeroDelta_coefficient_zero hs.2.le, zero_div]

theorem c_classical_integral_zero :
    (∫ x in bCut..WuPaper.R2SixthCount.beta,
      ∫ y in aCeiling..sigma, kernel wuLowerCoefficient x y) = 0 := by
  calc
    _ = ∫ x in bCut..WuPaper.R2SixthCount.beta, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le parameter_order.2.2.1.le] at hx
      calc
        _ = ∫ y in aCeiling..sigma, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro y hy
          rw [uIcc_of_le parameter_order.2.2.2.2.2.1.le] at hy
          exact c_classical_kernel_zero hx hy
        _ = 0 := by simp
    _ = 0 := by simp

theorem c_original_classical_count_lower (N : ℕ) :
    (4 * (∫ x in bCut..WuPaper.R2SixthCount.beta,
      ∫ y in aCeiling..sigma, kernel wuLowerCoefficient x y)) *
        (wuSingularSeries N * N / log (N : ℝ) ^ 2) ≤ (countC N : ℝ) := by
  rw [c_classical_integral_zero, mul_zero, zero_mul]
  exact_mod_cast rectangle_count_nonneg N bCut WuPaper.R2SixthCount.beta aCeiling sigma

#check @WuPaper.R2SixthCount.c_classical_kernel_zero
#check @WuPaper.R2SixthCount.c_classical_integral_zero
#check @WuPaper.R2SixthCount.c_original_classical_count_lower
#print axioms WuPaper.R2SixthCount.c_classical_kernel_zero
#print axioms WuPaper.R2SixthCount.c_classical_integral_zero
#print axioms WuPaper.R2SixthCount.c_original_classical_count_lower
end WuPaper.R2SixthCount
