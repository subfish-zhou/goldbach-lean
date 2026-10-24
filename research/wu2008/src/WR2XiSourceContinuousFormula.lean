import WR2XiSourceContinuousCount

noncomputable section
namespace WuPaper.R2Xi.SourceContinuousCount
open Wu2008DoubleSieve Wu08TerminalAlignment Wu08OriginalFourWeights SourceLedger

/-- Every classical slot and every currently composed source gain appears once. -/
theorem coefficient_exact : coefficient =
    (3*firstMain+secondMain-thirdMain-fourthMain+fifthMain+sixthMain-
      2*seventhMain-eighthMain-ninthMain-original10-original11+
      SourceSingle.amount+SourceFifth.amount+WuSource.SrcSingle.psiSevenPaid+SourceSixth.amount)/4 := by
  unfold coefficient remainderCoefficient SourceBlock.coefficient
  rw [Wu08FourMother.originalIntegral_false, Wu08FourMother.originalIntegral_true,
    ← U8CanonicalMother.L_eq_oldSmallIntegral]
  unfold sixthMain seventhMain eighthMain ninthMain
  ring

end WuPaper.R2Xi.SourceContinuousCount
#print axioms WuPaper.R2Xi.SourceContinuousCount.coefficient_exact
