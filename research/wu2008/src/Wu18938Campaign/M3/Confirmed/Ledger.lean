import Wu18938Campaign.M3.Confirmed.G2
import Wu08OriginalFourWeights

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights

def signedOriginalFunctions (δ G3 G4 G5 G6 : ℝ) : ℝ :=
  (3 * firstMain + secondMain - thirdMain - fourthMain + fifthMain + sixthMain -
    2 * seventhMain - eighthMain - ninthMain - original10 - original11 +
    8 * wuImprovementLimit false δ (103 / 25) + G3 + G4 + G5 + G6) / 4

theorem signed_original_functions_lower {δ G3 G4 G5 G6 : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hh42 : (6440 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (21 / 5))
    (hH32 : (52233 / 10000000 : ℝ) ≤ wuImprovementLimit true δ (16 / 5))
    (hpair : original10 + original11 < (851 / 1250 : ℝ))
    (hC1 : (14900897 / 1000000 : ℝ) ≤ firstMain)
    (hC2 : (9103015 / 1000000 : ℝ) ≤ secondMain)
    (hC3 : thirdMain ≤ (23652925 / 1000000 : ℝ))
    (hC4 : fourthMain ≤ (19643510 / 1000000 : ℝ))
    (hC5 : (1654808 / 1000000 : ℝ) ≤ fifthMain)
    (hC6 : (3819092 / 1000000 : ℝ) ≤ sixthMain)
    (hC7 : seventhMain ≤ (585179 / 1000000 : ℝ))
    (hC8 : eighthMain ≤ (5279581 / 1000000 : ℝ))
    (hC9 : ninthMain ≤ (5372410 / 1000000 : ℝ))
    (hG3 : (39890 / 1000000 : ℝ) ≤ G3)
    (hG4 : (8860 / 1000000 : ℝ) ≤ G4)
    (hG5 : (1359 / 1000000 : ℝ) ≤ G5)
    (hG6 : (60469 / 1000000 : ℝ) ≤ G6) :
    originalNumericLedger < signedOriginalFunctions δ G3 G4 G5 G6 ∧
      (899 / 1000 : ℝ) < signedOriginalFunctions δ G3 G4 G5 G6 := by
  have hg2 := correctedG2_actual_node hd hh hh42 hH32
  have hledger : originalNumericLedger < signedOriginalFunctions δ G3 G4 G5 G6 := by
    unfold originalNumericLedger signedOriginalFunctions
    linarith only [hg2, hpair, hC1, hC2, hC3, hC4, hC5, hC6,
      hC7, hC8, hC9, hG3, hG4, hG5, hG6]
  exact ⟨hledger, originalNumericLedger_gt.trans hledger⟩

end Wu18938Campaign.M3.Confirmed
