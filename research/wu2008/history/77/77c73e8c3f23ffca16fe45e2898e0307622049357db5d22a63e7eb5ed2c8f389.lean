import W07DensityConsumerV2

noncomputable section
namespace WuTarget.W07
open NodeExtension ActualNineFeedback Wu2008DoubleSieve Wu04Bypass
open scoped BigOperators

theorem paid_v8_gain (i : Fin 4) :
    (1 : ℝ) / 20000 < ∑ k : Fin 9, paidTable i k * v8 k := by
  fin_cases i <;> norm_num [Fin.sum_univ_succ, paidTable, v8]

theorem density_v8_gain (i : Fin 4) :
    (1 : ℝ) / 20000 < densityMoment (coupledRow i) v8 / 5 :=
  (paid_v8_gain i).trans_le (paidTable_sum_le i v8 v8_nonneg)

theorem paid_v8_matrix (i : Fin 4) :
    matrixApply paidMatrix v8 (embedFour i) = ∑ k : Fin 9, paidTable i k * v8 k := by
  unfold matrixApply
  apply Finset.sum_congr rfl
  intro k _
  rw [paidMatrix, dif_pos (show (embedFour i).val < 4 from i.isLt)]
  rfl

theorem paid_v8_actual_with_gain :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d →
        (∀ i : Fin 9, base i - deltaLoss δ * loss i +
          (∑ k : Fin 9, (M i k + paidMatrix i k) * v8 k) ≤ actualNine δ i) ∧
        (∀ i : Fin 4, (1 : ℝ) / 20000 < matrixApply paidMatrix v8 (embedFour i)) := by
  obtain ⟨d, hd, hcap, hpaid⟩ := paid_v8_actual
  refine ⟨d, hd, hcap, fun δ hδ hsmall => ⟨hpaid δ hδ hsmall, ?_⟩⟩
  intro i
  rw [paid_v8_matrix]
  exact paid_v8_gain i

end WuTarget.W07
