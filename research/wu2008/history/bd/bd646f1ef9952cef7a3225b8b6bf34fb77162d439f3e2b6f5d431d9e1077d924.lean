import MathlibNt.Wu2008DoubleSieve.TableGainKernel

/-!
# Actual upper-tail transport from the nine original seed coordinates
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped BigOperators Interval

noncomputable def tableGainL (v : ℝ) (j : Fin 9) : ℝ :=
  ∫ x in tableFeedbackR j.val..tableFeedbackR (j.val + 1), tableGainKernel v x

theorem tableGainL_nonneg {v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) (j : Fin 9) :
    0 ≤ tableGainL v j := by
  apply intervalIntegral.integral_nonneg (tableFeedbackR_monotone (Nat.le_succ j.val))
  intro x hx
  have hsub := tableFeedback_cell_subset tableFeedbackR_monotone
    tableFeedbackR_first tableFeedbackR_last j.isLt
  rw [uIcc_of_le (tableFeedbackR_monotone (Nat.le_succ j.val)),
    uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hsub
  exact tableGainKernel_nonneg hv hv5 (hsub hx)

theorem tableGain_actual_upper_tail {δ v : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    (∑ j : Fin 9, tableGainL v j * tableFeedbackActualVector δ j) ≤
      wuImprovementLimit true δ v := by
  have hp := tableFeedback_partition_lower hδ hδhi tableFeedbackR_monotone
    tableFeedbackR_first tableFeedbackR_last (tableGainKernel_intervalIntegrable hv hv5)
    (tableGainKernel_actual_intervalIntegrable hδ hδhi hv hv5)
    (fun x hx => tableGainKernel_nonneg hv hv5 hx)
  have heq : (∑ j : Fin 9, tableGainL v j * tableFeedbackActualVector δ j) =
      ∑ k ∈ Finset.range 9, wuImprovementLimit true δ (tableFeedbackR (k + 1)) *
        ∫ x in tableFeedbackR k..tableFeedbackR (k + 1), tableGainKernel v x := by
    simp only [tableGainL, tableFeedbackActualVector]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      (∫ x in tableFeedbackR k..tableFeedbackR (k + 1), tableGainKernel v x) *
        wuImprovementLimit true δ (tableFeedbackR (k + 1))) 9]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [heq]
  exact hp.trans (wuImprovementLimit_firstFeedback_62 hδ hδhi hv hv5)

theorem tableGainKernel_five {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 3) :
    tableGainKernel 5 x = 0 := by
  unfold tableGainKernel
  rw [show (4 : ℝ) / (5 - 1) = 1 by norm_num, log_one, mul_zero, zero_add]
  by_cases hm : x ∈ Icc ((5 : ℝ) - 2) 3
  · have he : x = 3 := by linarith [hm.1, hx.2]
    subst x
    norm_num
  · simp only [indicator_of_notMem hm, zero_div, zero_mul]

theorem tableGainL_five (j : Fin 9) : tableGainL 5 j = 0 := by
  have heq : tableGainL 5 j =
      ∫ x in tableFeedbackR j.val..tableFeedbackR (j.val + 1), (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx13 := tableFeedback_cell_subset tableFeedbackR_monotone
      tableFeedbackR_first tableFeedbackR_last j.isLt hx
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hx13
    exact tableGainKernel_five hx13
  rw [heq]
  simp

end Wu2008DoubleSieve
