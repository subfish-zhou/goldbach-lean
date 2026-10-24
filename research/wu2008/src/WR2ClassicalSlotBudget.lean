import WR2XiSourceFinalBudget
import WSrcFourEnclosureFine
import WR2ClassicalThirdFourth

noncomputable section
namespace WuPaper.ClassicalSlots
open Wu08TerminalAlignment Wu08OriginalFourWeights

/-- Explicit sufficient precision for each original slot; the four-prime cost is already paid. -/
theorem classical_lower_of_slots
    (h1 : (1490088:ℝ)/100000 ≤ firstMain)
    (h2 : (9103014:ℝ)/1000000 ≤ secondMain)
    (h4 : fourthMain ≤ (1964373:ℝ)/100000)
    (h5 : (165533:ℝ)/100000 ≤ fifthMain)
    (h6 : (381909:ℝ)/100000 ≤ sixthMain)
    (h7 : seventhMain ≤ (29259:ℝ)/50000)
    (h8 : eighthMain ≤ (13199:ℝ)/2500)
    (h9 : ninthMain ≤ (537242:ℝ)/100000) :
    (17401:ℝ)/20000 ≤ R2Xi.SourceContinuousCount.classicalPart := by
  have h3 := ClassicalThirdFourth.third_upper_of_fourth h4
  have hp := WuSource.SrcFourEnclosure.original_pair_upper
  unfold R2Xi.SourceContinuousCount.classicalPart
  linarith only [h1,h2,h3,h4,h5,h6,h7,h8,h9,hp]

end WuPaper.ClassicalSlots
#print axioms WuPaper.ClassicalSlots.classical_lower_of_slots
