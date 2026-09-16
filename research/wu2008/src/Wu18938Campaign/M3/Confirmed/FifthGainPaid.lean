import Wu18938Campaign.M3.Confirmed.FifthGainNodes

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.FifthGainNodes

open Real Wu2008DoubleSieve NodeExtension WuTarget
open FirstFeedbackIntegrals FirstErrorFullPayment RemainingHf SharpLogRecurrence
open F1FullRecoveryPayment JointLogTotalComparison Wu04FactorEnvelopes
open scoped BigOperators

def fixedUpper (k : Fin 19) : ℝ :=
  ![5177801,4387580,3702256,3107748,2592408,2146501,1761821,
    1431393,1149247,910242,709923,544408,409880,302107,216791,
    150290,98896,58606,26222] k / (1000000000:ℝ)

attribute [local simp] upperPaid tailPaid W02.tailLeft upperNode upperLeft rNode
  sourceVector W06.sigmaCoeff W06.massLower W06.denominatorLower
  TableBounds.logLower paidCell cellScale beta signed splitLower splitUpper
  basicLower basicUpper ea eb ec ed qa qb qc qd qe residualPrimitive residualDenom
  leftFactor rightFactor lowerLog upperLog V lowerGapPayment upperGapPayment
  F1LowerResidual.payment F1LowerResidual.denom fixedUpper

theorem fixed_upper_0 : fixedUpper 0 ≤ upperPaid 11 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_1 : fixedUpper 1 ≤ upperPaid 12 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_2 : fixedUpper 2 ≤ upperPaid 13 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_3 : fixedUpper 3 ≤ upperPaid 14 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_4 : fixedUpper 4 ≤ upperPaid 15 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_5 : fixedUpper 5 ≤ upperPaid 16 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_6 : fixedUpper 6 ≤ upperPaid 17 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_7 : fixedUpper 7 ≤ upperPaid 18 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_8 : fixedUpper 8 ≤ upperPaid 19 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_9 : fixedUpper 9 ≤ upperPaid 20 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_10 : fixedUpper 10 ≤ upperPaid 21 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_11 : fixedUpper 11 ≤ upperPaid 22 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_12 : fixedUpper 12 ≤ upperPaid 23 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_13 : fixedUpper 13 ≤ upperPaid 24 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_14 : fixedUpper 14 ≤ upperPaid 25 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_15 : fixedUpper 15 ≤ upperPaid 26 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_16 : fixedUpper 16 ≤ upperPaid 27 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_17 : fixedUpper 17 ≤ upperPaid 28 := by norm_num [Fin.sum_univ_succ]
theorem fixed_upper_18 : fixedUpper 18 ≤ upperPaid 29 := by norm_num [Fin.sum_univ_succ]

theorem fixed_upper_paid (k : Fin 19) : fixedUpper k ≤ upperPaid (11+k) := by
  fin_cases k
  · exact fixed_upper_0
  · exact fixed_upper_1
  · exact fixed_upper_2
  · exact fixed_upper_3
  · exact fixed_upper_4
  · exact fixed_upper_5
  · exact fixed_upper_6
  · exact fixed_upper_7
  · exact fixed_upper_8
  · exact fixed_upper_9
  · exact fixed_upper_10
  · exact fixed_upper_11
  · exact fixed_upper_12
  · exact fixed_upper_13
  · exact fixed_upper_14
  · exact fixed_upper_15
  · exact fixed_upper_16
  · exact fixed_upper_17
  · exact fixed_upper_18

end Wu18938Campaign.M3.Confirmed.FifthGainNodes
