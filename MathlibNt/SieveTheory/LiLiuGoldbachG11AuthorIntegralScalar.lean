import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorIntegralBound

open MeasureTheory Set
open scoped Interval BigOperators
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
theorem g11Author_log53_bounds :
    (473784352085 / 1000000000000 : ℝ) ≤ Real.log (53 / 33 : ℝ) ∧
      Real.log (53 / 33 : ℝ) ≤ 473784352086 / 1000000000000 := by
  have hl := Real.sum_range_le_log_div
    (by norm_num : (0 : ℝ) ≤ 10 / 43) (by norm_num : (10 / 43 : ℝ) < 1) 12
  have hu := Real.log_div_le_sum_range_add
    (by norm_num : (0 : ℝ) ≤ 10 / 43) (by norm_num : (10 / 43 : ℝ) < 1) 12
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

theorem g11Author_log40_bounds :
    (192371892647 / 1000000000000 : ℝ) ≤ Real.log (40 / 33 : ℝ) ∧
      Real.log (40 / 33 : ℝ) ≤ 192371892648 / 1000000000000 := by
  have hl := Real.sum_range_le_log_div
    (by norm_num : (0 : ℝ) ≤ 7 / 73) (by norm_num : (7 / 73 : ℝ) < 1) 12
  have hu := Real.log_div_le_sum_range_add
    (by norm_num : (0 : ℝ) ≤ 7 / 73) (by norm_num : (7 / 73 : ℝ) < 1) 12
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

theorem g11Author_primitives_scalar_bound :
    (561522 / 1000000 : ℝ) *
      ((36 / 5 : ℝ) * (g11AuthorMajorantPrimitive (1 / 10) -
        g11AuthorMajorantPrimitive (4 / 53)) +
      8 * (g11AuthorPrimitive0 (4 / 33) - g11AuthorPrimitive0 (1 / 10))) ≤
        10191 / 100000 := by
  obtain ⟨ha, hA⟩ := g11Author_log53_bounds
  obtain ⟨hc, hC⟩ := g11Author_log40_bounds
  have ha2 := pow_le_pow_left₀ (by norm_num) ha 2
  have hA2 := pow_le_pow_left₀ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 53 / 33)) hA 2
  have ha3 := pow_le_pow_left₀ (by norm_num) ha 3
  have hA3 := pow_le_pow_left₀ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 53 / 33)) hA 3
  have hc2 := pow_le_pow_left₀ (by norm_num) hc 2
  have hC2 := pow_le_pow_left₀ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 40 / 33)) hC 2
  have hc3 := pow_le_pow_left₀ (by norm_num) hc 3
  have hC3 := pow_le_pow_left₀ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 40 / 33)) hC 3
  norm_num [g11AuthorMajorantPrimitive, g11AuthorPrimitive0, g11AuthorPrimitive1,
    g11AuthorPrimitiveN, Finset.sum_range_succ]
  linarith only [ha, hA, hc, hC, ha2, hA2, ha3, hA3, hc2, hC2, hc3, hC3]

/-- Scalar certification of the author integral only; not an actual G11 bound. -/
theorem goldbachG11PrimeIntegral_author_scalar_le_10191 :
    (561522 / 1000000 : ℝ) * goldbachG11PrimeIntegral goldbachG11AuthorWeight ≤
      10191 / 100000 := by
  exact (mul_le_mul_of_nonneg_left goldbachG11PrimeIntegral_author_le_primitives
    (by norm_num : (0 : ℝ) ≤ 561522 / 1000000)).trans g11Author_primitives_scalar_bound

#check g11Author_log53_bounds
#print axioms g11Author_log53_bounds
#check g11Author_log40_bounds
#print axioms g11Author_log40_bounds
#check g11Author_primitives_scalar_bound
#print axioms g11Author_primitives_scalar_bound
#check goldbachG11PrimeIntegral_author_scalar_le_10191
#print axioms goldbachG11PrimeIntegral_author_scalar_le_10191
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig