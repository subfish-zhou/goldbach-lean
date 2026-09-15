import SrcNineData

noncomputable section
namespace WuSource.SrcNine
open Wu2008DoubleSieve ActualNineFeedback NodeExtension
open Wu2008DoubleSieve.SharpLogRecurrence Wu2008DoubleSieve.JointLogTotalComparison
open FirstFeedbackIntegrals FirstErrorFullPayment RemainingHf F1FullRecoveryPayment
open Wu04FactorEnvelopes
open WuTarget
open scoped BigOperators

macro "src_nine_scalar" : tactic =>
  `(tactic| (
    norm_num only [matrixApply, Fin.sum_univ_succ]
    norm_num only [z, W09.seed, W09.seedQ,
    W17Joint.jointMatrix, W17Joint.rationalSigmaMatrix, W17Joint.rowWeightLower,
    W17Joint.eWeightLower, W17Joint.jWeightLower, W17Joint.remainderMatrix,
    W06.sigmaCoeff, W06.massLower, W06.denominatorLower,
    W04.extraMatrix_eq_table, W04.extraTable, W05.jTable,
    W05.coupledTable0_s, W05.coupledTable0_kappa2, W05.coupledTable0_kappa3,
    W05.coupledTable1_s, W05.coupledTable1_kappa2, W05.coupledTable1_kappa3,
    W05.coupledTable2_s, W05.coupledTable2_kappa2, W05.coupledTable2_kappa3,
    W05.coupledTable3_s, W05.coupledTable3_kappa2, W05.coupledTable3_kappa3,
    W05.firstTable0, W05.firstTable1, W05.firstTable2, W05.firstTable3,
    W05.firstTable4, W07.paidMatrix, W07.paidTable, W08.paidMatrix,
    cellLeft, upperNode, upperLeft, coupledRow, firstNode, firstS,
    SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
    SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
    SecondFunctionalParameters.row4]
    norm_num [paidCell, cellScale, beta, signed,
    splitLower, splitUpper, basicLower, basicUpper, ea, eb, ec, ed, qa, qb, qc, qd, qe,
    residualPrimitive, residualDenom, leftFactor, rightFactor, lowerLog, upperLog,
    V, lowerGapPayment, upperGapPayment, F1LowerResidual.payment, F1LowerResidual.denom]))

theorem row0 : z 0 ≤ W09.seed 0 + matrixApply W17Joint.jointMatrix z 0 := by
  src_nine_scalar

end WuSource.SrcNine
