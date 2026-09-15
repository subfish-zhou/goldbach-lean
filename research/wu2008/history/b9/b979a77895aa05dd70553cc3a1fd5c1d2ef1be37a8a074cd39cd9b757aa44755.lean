import MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableIntegral

/-!
# The actual finite-vector gain inside the admissible sixth integral
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Classical BigOperators

theorem truncatedSixthTable_kernel_actual_le {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (v : ℝ × ℝ) :
    (∑ j : Fin 9, truncatedSixthTableKernel δ j v * tableFeedbackActualVector δ j) ≤
      truncatedSixthMassHKernel δ v := by
  by_cases hv : truncatedSixthLowerAdmissibleRegion δ v.1 v.2
  · have hb := truncatedSixthLower_region_bounds hδ.le hv.1
    have hd : 0 < v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2) :=
      mul_pos (mul_pos hb.1 hb.2.1)
        ((mul_pos (by norm_num : (0 : ℝ) < 2) truncatedSixthLower_parameters.1).trans_le hb.2.2.1)
    have hgain := tableGain_actual_lower hδ (by linarith) hb.2.2.2.1
      (by linarith [hb.2.2.2.2])
    simp_rw [truncatedSixthTable_kernel_literal hδ.le, if_pos hv]
    rw [truncatedSixthMassHKernel, if_pos hv]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hgain hd.le
  · simp [truncatedSixthTable_kernel_literal hδ.le, truncatedSixthMassHKernel, hv]

theorem truncatedSixthTable_actual_gain_le {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    (∑ j : Fin 9, truncatedSixthTableBeta δ j * tableFeedbackActualVector δ j) ≤
      truncatedSixthLowerHadmdelta δ := by
  have hi (j : Fin 9) : Integrable (fun v : ℝ × ℝ =>
      truncatedSixthTableKernel δ j v * tableFeedbackActualVector δ j) :=
    (truncatedSixthTable_kernel_integrable δ j).mul_const _
  have hs : Integrable (fun v : ℝ × ℝ =>
      ∑ j : Fin 9, truncatedSixthTableKernel δ j v * tableFeedbackActualVector δ j) :=
    integrable_finsetSum _ (fun j _ => hi j)
  have hm := integral_mono hs (truncatedSixthMass_kernels_integrable hδ hδhi).2
    (truncatedSixthTable_kernel_actual_le hδ hδhi)
  have heq : (∑ j : Fin 9, truncatedSixthTableBeta δ j * tableFeedbackActualVector δ j) =
      4 * ∫ v : ℝ × ℝ,
        ∑ j : Fin 9, truncatedSixthTableKernel δ j v * tableFeedbackActualVector δ j := by
    rw [integral_finsetSum _ (fun j _ => hi j)]
    simp_rw [truncatedSixthTable_beta_integral hδ.le, integral_mul_const]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _)
  rw [heq, (truncatedSixthMass_literal_integrals hδ hδhi).2]
  exact mul_le_mul_of_nonneg_left hm (by norm_num)

end Wu2008DoubleSieve
