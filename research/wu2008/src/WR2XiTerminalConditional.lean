import WR2XiRationalTopArithmetic
import WR2XiRationalCandidate
import FirstFeedbackTerminalLower




/-! Analytic certification of all nine terminal-row entries of the rational candidate. -/
noncomputable section
namespace WuPaper.R2Xi.RationalCandidate
open Real NodeExtension ActualNineFeedback Wu2008DoubleSieve
open FirstFeedbackIntegrals Wu04WholeCollection
open scoped BigOperators

private theorem terminal_lower (k : Fin 9)
    (hs : (Xi2RationalTop.sigmaCoeff k : ℝ) ≤ aProfile (nineProfile (nodeBasis k))) :
    low 2 * (Xi2RationalTop.sigmaCoeff k : ℝ) + eCell 3 (upperLeft k) (upperNode k) ≤
      firstFeedback (nodeBasis k) 3 3 := by
  have h := terminal_feedback_paid (nodeBasis_nonneg k)
  have hl : 0 ≤ low (2:ℝ) := by
    norm_num [low, Wu04FactorEnvelopes.lower, Wu04FactorEnvelopes.leftFactor,
      Wu04FactorEnvelopes.rightFactor, SharpLogRecurrence.lowerLog]
  have he : eCells (nodeBasis k) 3 = eCell 3 (upperLeft k) (upperNode k) := by
    by_cases hk : k = 0 <;> norm_num [eCells, nodeBasis, cellLeft, upperLeft, hk]
  rw [he] at h
  exact (add_le_add (mul_le_mul_of_nonneg_left hs hl) le_rfl).trans h

private theorem terminal_arithmetic (k : Fin 9) :
    lowerMatrix 8 k ≤ low 2 * (Xi2RationalTop.sigmaCoeff k : ℝ) +
      eCell 3 (upperLeft k) (upperNode k) := by
  have hrow : lowerMatrix 8 = (![191/1000, 3/125, 1/40, 1/40, 13/500,
      13/500, 27/1000, 27/1000, 27/1000] : Fin 9 → ℝ) := rfl
  rw [hrow]
  fin_cases k <;>
    norm_num [lowerMatrix, Xi2RationalTop.sigmaCoeff, Xi2RationalTop.massLower,
      upperLeft, upperNode, eCell, ea, eb, ec, ed,
      signedLow, low, up, Wu04FactorEnvelopes.lower, Wu04FactorEnvelopes.upper,
      Wu04FactorEnvelopes.leftFactor, Wu04FactorEnvelopes.rightFactor,
      SharpLogRecurrence.lowerLog, SharpLogRecurrence.upperLog, JointLogTotalComparison.V]

theorem terminal_entries_of_sigma (k : Fin 9)
    (hs : (Xi2RationalTop.sigmaCoeff k : ℝ) ≤ aProfile (nineProfile (nodeBasis k))) :
    lowerMatrix 8 k ≤ correctedNineMatrix 8 k := by
  have h := (terminal_arithmetic k).trans (terminal_lower k hs)
  have hn : firstNode (4:Fin 5) = 3 := by norm_num [firstNode]
  change lowerMatrix 8 k ≤ firstFeedback (nodeBasis k) (firstNode 4) (firstS 4)
  have hS : firstS (4:Fin 5) = 3 := rfl
  simpa only [hn, hS] using h

end WuPaper.R2Xi.RationalCandidate

#print axioms WuPaper.R2Xi.RationalCandidate.terminal_entries_of_sigma
