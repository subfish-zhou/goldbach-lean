import WE02JointCreditRankOneStructure

noncomputable section
namespace WuTarget.E02JointCredit
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open scoped BigOperators

theorem rankOneSigmaMass_exact :
    rankOneSigmaMass = (57153427687978657391/77653743750000000000000 : ℝ) := by
  norm_num [rankOneSigmaMass, W06.sigmaLower, W06.sigmaCoeff, W06.massLower,
    W06.denominatorLower, Wu04Bypass.v8, Fin.sum_univ_succ]

def rankOneRowLower : Fin 9 → ℚ :=
  ![187615043/500000000000, 191387593/500000000000,
    380354511/1000000000000, 198824317/500000000000,
    406884743/1000000000000, 199668871/500000000000,
    391474491/1000000000000, 47735957/125000000000,
    368001753/1000000000000]

theorem rankOneRowLower_pos (i : Fin 9) : 0 < rankOneRowLower i := by
  fin_cases i <;> norm_num [rankOneRowLower]

theorem rankOneRowLower_le (i : Fin 9) : (rankOneRowLower i : ℝ) ≤ rankOneRows i := by
  unfold rankOneRows
  rw [rankOneSigmaMass_exact]
  fin_cases i <;>
    norm_num [rankOneRowLower, W09.increment, W17Joint.rowWeightLower,
      W17Joint.eWeightLower, W17Joint.jWeightLower, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4, firstS, firstNode]

theorem rankOneRowLower_le_difference (i : Fin 9) :
    (rankOneRowLower i : ℝ) ≤ difference i :=
  (rankOneRowLower_le i).trans (rankOneRows_le_difference i)

def rankOneQTransfer (j : Fin 21) : ℚ :=
  ∑ k : Fin 9, W02.qMatrix j k * rankOneRowLower k

theorem rankOneQTransfer_cast (j : Fin 21) :
    (rankOneQTransfer j : ℝ) =
      matrixApply W02.rationalMatrix (fun k => (rankOneRowLower k : ℝ)) j := by
  simp only [rankOneQTransfer, Rat.cast_sum, Rat.cast_mul, W02.qMatrix_cast, matrixApply]

theorem rankOneQTransfer_le (j : Fin 21) :
    (rankOneQTransfer j : ℝ) ≤ matrixApply W02.rationalMatrix difference j := by
  rw [rankOneQTransfer_cast]
  exact matrixApply_mono W02.rationalMatrix_nonneg rankOneRowLower_le_difference j

end WuTarget.E02JointCredit
