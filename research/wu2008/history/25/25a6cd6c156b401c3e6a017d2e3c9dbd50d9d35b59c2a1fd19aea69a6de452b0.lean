import W02Output0

namespace WuTarget.W02
open NodeExtension ActualNineFeedback

def lowerNumerators : Fin 21 → ℕ :=
  ![11285954, 10555082, 9824211, 9093339, 8362468, 7631596, 6900724,
    6169853, 5438981, 4708110, 3977238, 3246367, 2572621, 1983737,
    1503135, 1097159, 802059, 613247, 501236, 407071, 327026]

def lowerVector (j : Fin 21) : ℚ := (lowerNumerators j : ℚ) / 1000000000

theorem output_lower (j : Fin 21) : lowerVector j ≤ qOutput j := by
  fin_cases j
  · exact output0
  all_goals decide +kernel

theorem lowerVector_pos (j : Fin 21) : 0 < lowerVector j := by
  fin_cases j <;> norm_num [lowerVector, lowerNumerators]

theorem lowerVector_le_transfer (j : Fin 21) :
    (lowerVector j : ℝ) ≤ matrixApply transferMatrix Wu04Bypass.v8 j := by
  have h : (lowerVector j : ℝ) ≤ (qOutput j : ℝ) := by
    exact_mod_cast output_lower j
  exact h.trans (v8_output_le_transfer j)

theorem lowerVector_keeps_sigma (j : Fin 21) :
    (lowerVector j : ℝ) + aProfile (nineProfile Wu04Bypass.v8) * sigmaWeight j ≤
      matrixApply transferMatrix Wu04Bypass.v8 j := by
  have h : (lowerVector j : ℝ) ≤ (qOutput j : ℝ) := by
    exact_mod_cast output_lower j
  exact (add_le_add h le_rfl).trans (v8_output_keeps_sigma j)

theorem certified_twentyone_actual : ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d →
      (∀ i : Fin 9, Wu04Bypass.v8 i ≤ actualNine δ i) ∧
      (∀ j : Fin 21, (lowerVector j : ℝ) ≤
        Wu2008DoubleSieve.wuImprovementLimit false δ (rNode (j.val + 1))) ∧
      (∀ j : Fin 21, (lowerVector j : ℝ) +
          aProfile (nineProfile Wu04Bypass.v8) * sigmaWeight j ≤
        Wu2008DoubleSieve.wuImprovementLimit false δ (rNode (j.val + 1))) := by
  obtain ⟨d, hd, hcap, hh⟩ := Wu04Bypass.new_nine_and_twentyone_actual
  refine ⟨d, hd, hcap, ?_⟩
  intro δ hδ hr
  have hs := hh δ hδ hr
  exact ⟨hs.1, fun j => (lowerVector_le_transfer j).trans (hs.2 j),
    fun j => (lowerVector_keeps_sigma j).trans (hs.2 j)⟩

end WuTarget.W02
