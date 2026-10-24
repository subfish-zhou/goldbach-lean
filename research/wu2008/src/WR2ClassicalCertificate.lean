import WR2ClassicalKnownSlots
import WR2ClassicalFourthCertificate
import WR2ClassicalFifthCertificate
import WR2ClassicalSixthCertificate

noncomputable section
namespace WuPaper.ClassicalSlots

/-- All original classical slots, using the fourth slot to control the third. -/
theorem classical_lower : (17401:ℝ)/20000 ≤ R2Xi.SourceContinuousCount.classicalPart :=
  classical_lower_of_three_slots ClassicalFourthConditions.fourth_main_upper
    ClassicalFifthRational.fifth_main_lower ClassicalSixthRational.sixth_main_lower

/-- The original Wu bound after all classical and improvement integrals are certified. -/
theorem one894 :
    ∃ T ≥ 512, ∀ N ≥ T, Even N → ∃ p r q : ℕ,
      p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧ N=p+r*q ∧ r^500≤q^447 :=
  R2Xi.SixthContinuous.one894_of_classical classical_lower

end WuPaper.ClassicalSlots
#print axioms WuPaper.ClassicalSlots.classical_lower
#print axioms WuPaper.ClassicalSlots.one894
