import Wu08RecoveryOriginalPair
import Wu08RecoveredInputs

noncomputable section
open Real MeasureTheory Wu2008DoubleSieve
namespace Wu08FourMother
open Wu08FirstPrimeFour.SmallBoundaryRecovery Wu08OriginalFourWeights

theorem originalIntegral_false : originalIntegral false = original10 := by
  rw [originalIntegral_literal]
  simp only [Bool.false_eq_true, ite_false]
  unfold original10 original
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  ring

theorem originalIntegral_true : originalIntegral true = original11 := by
  rw [originalIntegral_literal]
  simp only [ite_true]
  unfold original11 original
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  ring

/-- The recovered amount is a replacement in the two original negative slots. -/
def restoredDebit : ℝ := debit10+debit11

theorem restoredDebit_exact : restoredDebit =
    8*FourRoughClosedMass.I10+8*FourRoughClosedMass.I11-
      originalIntegral false-originalIntegral true := by
  rw [originalIntegral_false,originalIntegral_true]
  have h10 := actual_tenth_debit
  have h11 := actual_eleventh_debit
  unfold Wu08TerminalAlignment.tenthCurrent at h10
  unfold Wu08TerminalAlignment.eleventhCurrent at h11
  unfold restoredDebit
  linarith only [h10,h11]

theorem restoredDebit_nonneg : 0 ≤ restoredDebit :=
  add_nonneg debits_nonnegative.1 debits_nonnegative.2

end Wu08FourMother

#check @TruncatedFourPhysical.original_sums_upper
#check @FourClassical.physical10_physical11_sum_classical_upper
#print TruncatedFourPhysical.Q10
#print TruncatedFourPhysical.Q11
#print TruncatedFourPhysical.T10
#print TruncatedFourPhysical.T11
#print fourModulusProduct
#check @HighSixDeltaLimit.coefficient_close
#check @U8CanonicalMother.scale_eq_liu
#check @MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct_pos
#check @Wu08FourMother.originalIntegral_false
#print axioms Wu08FourMother.originalIntegral_false
#check @Wu08FourMother.originalIntegral_true
#print axioms Wu08FourMother.originalIntegral_true
#check @Wu08FourMother.restoredDebit_exact
#print axioms Wu08FourMother.restoredDebit_exact
#check @Wu08FourMother.restoredDebit_nonneg
#print axioms Wu08FourMother.restoredDebit_nonneg
