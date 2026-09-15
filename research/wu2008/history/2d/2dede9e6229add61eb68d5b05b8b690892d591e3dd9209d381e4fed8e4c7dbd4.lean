import Wu04BypassRow0
import Wu04BypassRow1
import Wu04BypassRow2
import Wu04BypassRow3
import Wu04BypassRow4
import Wu04BypassRow5
import Wu04BypassRow6
import Wu04BypassRow7
import Wu04BypassRow8
import Wu04BypassRound0
import Wu04BypassRound1
import Wu04BypassRound2
import Wu04BypassRound3
import Wu04BypassRound4
import Wu04BypassRound5
import Wu04BypassRound6
import Wu04BypassRound7

noncomputable section
namespace Wu04Bypass
open ActualNineFeedback NodeExtension Wu2008DoubleSieve
open scoped BigOperators

theorem M_le_actual (i k : Fin 9) : M i k ≤ feedbackMatrix i k := by
  fin_cases i
  · exact (matrix_row0 k).trans (elementaryMatrix_le _ k)
  · exact (matrix_row1 k).trans (elementaryMatrix_le _ k)
  · exact (matrix_row2 k).trans (elementaryMatrix_le _ k)
  · exact (matrix_row3 k).trans (elementaryMatrix_le _ k)
  · exact (matrix_row4 k).trans (elementaryMatrix_le _ k)
  · exact (matrix_row5 k).trans (elementaryMatrix_le _ k)
  · exact (matrix_row6 k).trans (elementaryMatrix_le _ k)
  · exact (matrix_row7 k).trans (elementaryMatrix_le _ k)
  · exact (matrix_row8 k).trans (elementaryMatrix_le _ k)

/-- No inverse or fixed-point theorem is used in this update. -/
theorem paid_update {δ : ℝ}
    (hs : ∀ i, NineFeedbackStrength.publication i +
      matrixApply feedbackMatrix (actualNine δ) i ≤ actualNine δ i)
    {x y : Fin 9 → ℝ} (hx : ∀ k, x k ≤ actualNine δ k)
    (hn : ∀ k, 0 ≤ x k) (hy : ∀ i, y i ≤ v0 i + ∑ k : Fin 9, M i k * x k) :
    ∀ i, y i ≤ actualNine δ i := by
  intro i
  have hm : (∑ k : Fin 9, M i k * x k) ≤ matrixApply feedbackMatrix x i :=
    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (M_le_actual i k) (hn k))
  have ha := matrixApply_mono feedbackMatrix_nonneg hx i
  have hh := hs i
  rw [← v0_eq_publication] at hh
  linarith only [hy i, hm, ha, hh]

/-- A new explicit nine-vector, using only paid forcing and eight certified updates. -/
theorem new_nine_actual : ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i : Fin 9, v8 i ≤ actualNine δ i := by
  obtain ⟨d, hd, hcap, hs⟩ := NineFeedbackStrength.actual_same_delta
  refine ⟨d, hd, hcap, ?_⟩
  intro δ hδ hr
  have hh := hs δ hδ hr
  have hn := actualNine_nonneg hδ (hr.trans hcap)
  have h0 : ∀ i, v0 i ≤ actualNine δ i := by
    rw [v0_eq_publication]
    intro i
    exact (le_add_of_nonneg_right
      (matrixApply_nonneg feedbackMatrix_nonneg hn i)).trans (hh i)
  have h1 := paid_update hh h0 v0_nonneg round0
  have h2 := paid_update hh h1 v1_nonneg round1
  have h3 := paid_update hh h2 v2_nonneg round2
  have h4 := paid_update hh h3 v3_nonneg round3
  have h5 := paid_update hh h4 v4_nonneg round4
  have h6 := paid_update hh h5 v5_nonneg round5
  have h7 := paid_update hh h6 v6_nonneg round6
  have h8 := paid_update hh h7 v7_nonneg round7
  exact h8

theorem new_nine_and_twentyone_actual : ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d →
      (∀ i : Fin 9, v8 i ≤ actualNine δ i) ∧
      (∀ j : Fin 21, matrixApply transferMatrix v8 j ≤
        wuImprovementLimit false δ (rNode (j.val + 1))) := by
  obtain ⟨d, hd, hcap, hh⟩ := new_nine_actual
  refine ⟨d, hd, hcap, ?_⟩
  intro δ hδ hr
  refine ⟨hh δ hδ hr, ?_⟩
  intro j
  exact (matrixApply_mono transferMatrix_nonneg (hh δ hδ hr) j).trans
    (actual_twentyone_matrix hδ (hr.trans hcap) j)

theorem new_vector_strictly_improves_seed (i : Fin 9) : v0 i < v8 i := by
  fin_cases i <;> norm_num [v0, v8]

theorem new_vector_positive (i : Fin 9) : 0 < v8 i :=
  lt_of_le_of_lt (v0_nonneg i) (new_vector_strictly_improves_seed i)

end Wu04Bypass
