import WR2XiRationalTopArithmetic
import WR2XiRationalCandidate
import FirstFeedbackJPayment




/-! Rational certificates for the four nonterminal first-functional rows. -/
noncomputable section
namespace WuPaper.R2Xi.RationalCandidate
open Real NodeExtension ActualNineFeedback Wu2008DoubleSieve
open FirstFeedbackIntegrals Wu04WholeCollection
open scoped BigOperators

private def firstEntryLower (i : Fin 4) (k : Fin 9) : ℝ :=
  firstACoefficient (firstNode i.castSucc) (firstS i.castSucc) *
    (Xi2RationalTop.sigmaCoeff k : ℝ) +
    firstResidual (nodeBasis k) (firstNode i.castSucc) (firstS i.castSucc)

private theorem first_entry_lower (i : Fin 4) (k : Fin 9)
    (hsigma : (Xi2RationalTop.sigmaCoeff k : ℝ) ≤ aProfile (nineProfile (nodeBasis k))) :
    firstEntryLower i k ≤
      firstFeedback (nodeBasis k) (firstNode i.castSucc) (firstS i.castSucc) := by
  have hg := first_geometry i.castSucc
  have hS : 3 < firstS i.castSucc := by fin_cases i <;> norm_num [firstS]
  have hcell : firstS i.castSucc - 2 ≤ upperNode 0 := by
    fin_cases i <;> norm_num [firstS, upperNode]
  have hsS : firstNode i.castSucc ≤ firstS i.castSucc := hg.2.1.trans hg.2.2.1
  have h := firstFeedback_affine_lower (nodeBasis_nonneg k) hg.1 hS hg.2.2.2.1
    hsS hg.2.2.2.2 hcell
  have ha : 0 ≤ firstACoefficient (firstNode i.castSucc) (firstS i.castSucc) := by
    fin_cases i <;> norm_num [firstACoefficient, jWeight, firstNode, firstS,
      low, Wu04FactorEnvelopes.lower, Wu04FactorEnvelopes.leftFactor,
      Wu04FactorEnvelopes.rightFactor, SharpLogRecurrence.lowerLog]
  exact (add_le_add (mul_le_mul_of_nonneg_left
    hsigma ha) le_rfl).trans h

private theorem firstEntryLower_basis (i : Fin 4) (k : Fin 9) :
    firstEntryLower i k =
      firstACoefficient (firstNode i.castSucc) (firstS i.castSucc) * (Xi2RationalTop.sigmaCoeff k : ℝ) +
      (eCell (firstS i.castSucc) (cellLeft (firstS i.castSucc - 2) k) (upperNode k) +
        (low (upperNode k / cellLeft (firstS i.castSucc - 2) k) *
          jWeight (firstNode i.castSucc) (firstS i.castSucc) +
          (if k = 0 then jCurvePaid (firstNode i.castSucc) (firstS i.castSucc) else 0)) / 2) := by
  simp [firstEntryLower, firstResidual, eCells, tailCells, nodeBasis, eq_comm]

set_option maxHeartbeats 1600000 in
private theorem first_entry_arithmetic (i : Fin 4) (k : Fin 9) :
    lowerMatrix (Fin.natAdd 4 i.castSucc) k ≤ firstEntryLower i k := by
  rw [firstEntryLower_basis]
  fin_cases i <;> fin_cases k <;>
    norm_num [lowerMatrix, Matrix.cons_val, Fin.natAdd, firstACoefficient,
      firstNode, firstS, eCells, tailCells, nodeBasis, cellLeft, upperLeft, upperNode,
      Fin.sum_univ_succ, jWeight, jCurvePaid,
      Wu04FactorJPrimitive.c0, Wu04FactorJPrimitive.c1,
      Wu04FactorJPrimitive.h2, Wu04FactorJPrimitive.h3, Wu04FactorJPrimitive.cubic,
      Xi2RationalTop.sigmaCoeff, Xi2RationalTop.massLower,
      eCell, ea, eb, ec, ed, signedLow, low, up,
      Wu04FactorEnvelopes.lower, Wu04FactorEnvelopes.upper,
      Wu04FactorEnvelopes.leftFactor, Wu04FactorEnvelopes.rightFactor,
      SharpLogRecurrence.lowerLog, SharpLogRecurrence.upperLog, JointLogTotalComparison.V]

theorem first_four_entries_of_sigma (i : Fin 4) (k : Fin 9)
    (hsigma : (Xi2RationalTop.sigmaCoeff k : ℝ) ≤ aProfile (nineProfile (nodeBasis k))) :
    lowerMatrix (Fin.natAdd 4 i.castSucc) k ≤
      correctedNineMatrix (Fin.natAdd 4 i.castSucc) k := by
  simpa only [correctedNineMatrix, Fin.addCases_right] using (first_entry_arithmetic i k).trans (first_entry_lower i k hsigma)

end WuPaper.R2Xi.RationalCandidate

#print axioms WuPaper.R2Xi.RationalCandidate.first_four_entries_of_sigma
