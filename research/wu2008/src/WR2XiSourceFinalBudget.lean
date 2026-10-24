import WR2XiSourceRefinedTarget
import WR2XiSourceSingleCertificate
import WR2XiSourceFifthCertificate
import WR2SevenGainRational

noncomputable section
namespace WuPaper.R2Xi.SourceContinuousCount
open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights WuSource.SrcSingle

/-- The unchanged original classical slots, with both four-prime costs. -/
def classicalPart : ℝ :=
  (3*firstMain+secondMain-thirdMain-fourthMain+fifthMain+sixthMain-
    2*seventhMain-eighthMain-ninthMain-original10-original11)/4

theorem coefficient_split : coefficient = classicalPart+
    (SourceSingle.amount+SourceFifth.amount+psiSevenPaid+SourceSixth.amount)/4 := by
  rw [coefficient_exact]
  unfold classicalPart
  ring

/-- These two integral bounds remain obligations, not certified numbers. -/
theorem target_of_integral_bounds
    (hc : (17401/20000 : ℝ) ≤ classicalPart)
    (h6 : (283/5000 : ℝ) ≤ SourceSixth.amount) :
    (4491/5000 : ℝ) ≤ coefficient := by
  rw [coefficient_split]
  have hs := SourceRational.SingleCertificate.single_gain_lower
  have hf := SourceRational.fifth_gain_lower
  have hp := R2Seven.seven_gain_lower
  linarith only [hc,h6,hs,hf,hp]

theorem one894_of_integral_bounds
    (hc : (17401/20000 : ℝ) ≤ classicalPart)
    (h6 : (283/5000 : ℝ) ≤ SourceSixth.amount) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∃ p r q : ℕ, p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p+r*q ∧ r^500 ≤ q^447 :=
  one894_of_coefficient (target_of_integral_bounds hc h6)

end WuPaper.R2Xi.SourceContinuousCount
#print axioms WuPaper.R2Xi.SourceContinuousCount.one894_of_integral_bounds
