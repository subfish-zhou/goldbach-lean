import W03Consumer

namespace WuTarget.W03
open QuarterTrim NodeExtension ActualNineFeedback DirectFiniteF6 Wu2008DoubleSieve
open scoped BigOperators
noncomputable section

def paidWeights : Fin 21 → ℝ :=
  ![904256/6350645, 166848/907235, 1431616/6350645, 8027812/31753225,
    321920/1270129, 321920/1270129, 321920/1270129, 321920/1270129,
    321920/1270129, 321920/1270129, 321920/1270129, 321920/1270129,
    321920/1270129, 321920/1270129, 778874224/3270582175, 1251328/6350645,
    987648/6350645, 103424/907235, 460288/6350645, 196608/6350645, 7744/6182575]

theorem paidWeights_eq (j : Fin 21) : paidWeights j = rationalWeight j := by
  fin_cases j <;>
    norm_num [paidWeights, rationalWeight, cellArea, triangleArea, sumUpper, sumLower,
      denominatorCap, alpha, beta, rNode]

theorem paidWeights_pos (j : Fin 21) : 0 < paidWeights j := by
  rw [paidWeights_eq]
  exact rationalWeight_pos j

theorem paidWeights_le (j : Fin 21) : paidWeights j ≤ weight j := by
  rw [paidWeights_eq]
  exact rationalWeight_le j

theorem paid_weights_consumer {w : Fin 21 → ℝ} (hw : ∀ j, 0 ≤ w j) :
    (∑ j : Fin 21, paidWeights j * w j) ≤ Gamma w 0 :=
  lower_weights_consumer paidWeights_le hw

theorem frozen_paid_lower :
    (∑ j : Fin 21, paidWeights j * matrixApply transferMatrix Wu04Bypass.v8 j) ≤
      Gamma (matrixApply transferMatrix Wu04Bypass.v8) 0 :=
  paid_weights_consumer frozen_nonneg

theorem frozen_paid_Hadm_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1/100 ∧ ∀ δ : ℝ, 0 < δ → δ < d0 →
      (∑ j : Fin 21, paidWeights j * matrixApply transferMatrix Wu04Bypass.v8 j) - ε ≤
        truncatedSixthLowerHadmdelta δ := by
  simpa only [paidWeights_eq] using frozen_rational_Hadm_payment hε

end
end WuTarget.W03
