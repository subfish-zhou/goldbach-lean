import W17JointSplit

namespace WuTarget.W17Joint
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open ActualNineFeedback NodeExtension FirstFeedbackIntegrals FirstErrorFullPayment
open RemainingHf F1FullRecoveryPayment Wu04FactorEnvelopes

macro "w17_norm" : tactic => `(tactic|
  norm_num [jointMatrix, rationalSigmaMatrix, rowWeightLower, eWeightLower, jWeightLower,
    W06.sigmaCoeff, W06.massLower, W06.denominatorLower, remainderMatrix,
    W08.paidMatrix, W04.extraMatrix_eq_table, W04.extraTable,
    W05.jTable, W05.coupledTable0_s, W05.coupledTable0_kappa2, W05.coupledTable0_kappa3,
    W05.coupledTable1_s, W05.coupledTable1_kappa2, W05.coupledTable1_kappa3,
    W05.coupledTable2_s, W05.coupledTable2_kappa2, W05.coupledTable2_kappa3,
    W05.coupledTable3_s, W05.coupledTable3_kappa2, W05.coupledTable3_kappa3,
    W05.firstTable0, W05.firstTable1, W05.firstTable2, W05.firstTable3, W05.firstTable4,
    W07.paidMatrix, W07.paidTable,
    cellLeft, upperNode, upperLeft, coupledRow, SecondFunctionalPositive.parameters,
    SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
    SecondFunctionalParameters.row3, SecondFunctionalParameters.row4, firstS, firstNode,
    paidCell, cellScale, beta, signed, splitLower, splitUpper, basicLower, basicUpper,
    ea, eb, ec, ed, qa, qb, qc, qd, qe, residualPrimitive, residualDenom, leftFactor,
    rightFactor, lowerLog, upperLog, V, lowerGapPayment, upperGapPayment,
    F1LowerResidual.payment, F1LowerResidual.denom])

open Lean Elab Tactic Qq in
elab "w17_record " i:num k:num : tactic => do
  let target ← getMainTarget
  let lhs := target.getAppArgs[1]!
  let result ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) lhs
  let some value := result.toRat | throwError "Joint entry did not normalize to a rational"
  logInfo m!"W17ENTRY {i.getNat} {k.getNat} {value.num} {value.den}"

end WuTarget.W17Joint
