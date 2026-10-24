import WR2ClassicalCCertificate
import WR2ClassicalSecondCertificate
import WR2ClassicalSeventhCertificate
import WR2ClassicalEighthCertificate
import WR2ClassicalNinthCertificate
import WR2ClassicalSlotBudget
import WR2XiSixthCertificate

noncomputable section
namespace WuPaper.ClassicalSlots
open Wu08TerminalAlignment

/-- The remaining classical numerical obligations are exactly slots four, five and six. -/
theorem classical_lower_of_three_slots
    (h4 : fourthMain ≤ (1964373:ℝ)/100000)
    (h5 : (165533:ℝ)/100000 ≤ fifthMain)
    (h6 : (381909:ℝ)/100000 ≤ sixthMain) :
    (17401:ℝ)/20000 ≤ R2Xi.SourceContinuousCount.classicalPart := by
  apply classical_lower_of_slots ClassicalC.first_main_lower ClassicalSecond.second_main_lower
    h4 h5 h6 ClassicalSeventh.seventh_main_upper ClassicalEighth.eighth_main_upper
  have h := ClassicalNinth.ninth_main_upper
  norm_num only at h ⊢
  exact h

theorem one894_of_three_slots
    (h4 : fourthMain ≤ (1964373:ℝ)/100000)
    (h5 : (165533:ℝ)/100000 ≤ fifthMain)
    (h6 : (381909:ℝ)/100000 ≤ sixthMain) :
    ∃ T ≥ 512, ∀ N ≥ T, Even N → ∃ p r q : ℕ,
      p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧ N=p+r*q ∧ r^500≤q^447 :=
  R2Xi.SixthContinuous.one894_of_classical (classical_lower_of_three_slots h4 h5 h6)

end WuPaper.ClassicalSlots
#print axioms WuPaper.ClassicalSlots.classical_lower_of_three_slots
#print axioms WuPaper.ClassicalSlots.one894_of_three_slots
