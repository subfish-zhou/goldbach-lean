import MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableLimit

/-!
# Coefficient error paid against the bounded actual nine-vector

The actual vector retains its delta argument. Only explicit integral
coefficients are approximated; no gain continuity is assumed.
-/

namespace Wu2008DoubleSieve

open Set Real
open scoped Classical BigOperators
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem truncatedSixthTable_actual_vector_bounds {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (j : Fin 9) :
    0 ≤ tableFeedbackActualVector δ j ∧ tableFeedbackActualVector δ j ≤ 10 := by
  have hr := tableFeedback_endpoint_bounds j
  have hr0 : 0 < tableFeedbackR (j.val + 1) := by linarith [hr.1]
  have hA : wuUpperCoefficient (tableFeedbackR (j.val + 1)) = 1 := by
    unfold wuUpperCoefficient
    rw [jr1965F_eq_of_le_three hr.2]
    field_simp [hr0.ne', (exp_pos eulerMascheroniConstant).ne']
  have hb := wuImprovementLimit_bounds hδ (by linarith) hr.1 (by linarith [hr.2])
  refine ⟨hb.1, hb.2.1.trans ?_⟩
  rw [hA]
  norm_num

theorem truncatedSixthTable_coefficient_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
        (∑ j : Fin 9, truncatedSixthTableBeta 0 j * tableFeedbackActualVector δ j) ≤
          (∑ j : Fin 9, truncatedSixthTableBeta δ j * tableFeedbackActualVector δ j) + ε := by
  obtain ⟨δ0, hδ0, hδ0hi, hc⟩ := truncatedSixthTable_beta_close
    (show 0 < ε / 90 by positivity)
  refine ⟨δ0, hδ0, hδ0hi, ?_⟩
  intro δ hδ hsmall
  have hδhi : δ ≤ 1 / 10 := by linarith [hsmall.trans_le hδ0hi]
  have hterm (j : Fin 9) :
      (truncatedSixthTableBeta 0 j - truncatedSixthTableBeta δ j) *
        tableFeedbackActualVector δ j ≤ ε / 9 := by
    have hd := (abs_lt.mp (hc δ hδ hsmall j)).1
    have hd' : truncatedSixthTableBeta 0 j - truncatedSixthTableBeta δ j ≤ ε / 90 := by
      linarith
    have hx := truncatedSixthTable_actual_vector_bounds hδ hδhi j
    calc
      _ ≤ (ε / 90) * tableFeedbackActualVector δ j :=
        mul_le_mul_of_nonneg_right hd' hx.1
      _ ≤ (ε / 90) * 10 := mul_le_mul_of_nonneg_left hx.2 (by positivity)
      _ = ε / 9 := by ring
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  simp only [sub_mul, Finset.sum_sub_distrib] at hsum
  have hconst : (∑ _j : Fin 9, ε / 9) = ε := by simp; ring
  rw [hconst] at hsum
  linarith

end Wu2008DoubleSieve
