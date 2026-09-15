import SigmaInnerPaidOuter
import SigmaInnerProfileCoupled
namespace SigmaPrimitiveCells
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment
open scoped Interval BigOperators
noncomputable section

def cellMass (a b : ℝ) : ℝ := SigmaInnerPaid.primitive b-SigmaInnerPaid.primitive a

theorem cellMass_le {a b : ℝ} (ha : 1≤a) (hab : a≤b) (hb : b≤3) :
    cellMass a b ≤ SigmaInnerProfile.cellIntegral a b := by
  rw [cellMass,← SigmaInnerPaid.weight_integral ha hab]
  apply intervalIntegral.integral_mono_on hab
    (SigmaInnerPaid.weight_continuous (by linarith) hab).intervalIntegrable
    (SigmaInnerProfile.weight_continuous (by linarith) hab).intervalIntegrable
  intro t ht
  exact div_le_div_of_nonneg_right
    (SigmaInnerPaid.endpointPaid_le_kernel (ha.trans ht.1) (ht.2.trans hb)) (by linarith [ht.1])

def numerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9,z k*cellMass (upperLeft k) (upperNode k)

theorem numerator_le {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    numerator z ≤ SigmaInnerProfile.numerator z := by
  apply Finset.sum_le_sum
  intro k _
  have hb := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he] at hb
  exact mul_le_mul_of_nonneg_left (cellMass_le hb.1 hb.2.1 hb.2.2.1) (hz k)

/-- Finite elementary expression; endpoint logarithms have not yet been bounded. -/
def elementaryLower : ℝ := numerator NineFeedbackStrength.originalH/(1-SigmaRemaining.d0Paid)

theorem elementaryLower_le : elementaryLower ≤ SigmaInnerProfile.d0Lower NineFeedbackStrength.originalH :=
  div_le_div_of_nonneg_right (numerator_le CoupledIntegralRecovery.originalH_nonneg)
    (sub_pos.mpr SigmaRemaining.d0Paid_lt_one).le

/-- Keep the accepted old bound if the new endpoint payment loses more information. -/
def profileLower : ℝ := max (SigmaRemaining.finiteLower NineFeedbackStrength.originalH) elementaryLower

theorem profileLower_le : profileLower ≤ aProfile (nineProfile NineFeedbackStrength.originalH) :=
  max_le SigmaRemaining.original_finiteLower
    (elementaryLower_le.trans SigmaInnerProfile.original_d0Lower_le_profile)

theorem profileLower_pos : 0<profileLower :=
  SigmaRemaining.original_finiteLower_pos.trans_le (le_max_left _ _)

def coupledLower (p : Wu2008DoubleSieve.SecondFunctionalParameters) : ℝ :=
  SigmaRemaining.coupledLower p+CoupledFiniteAssembly.aCoefficient p*
    (profileLower-SigmaRemaining.finiteLower NineFeedbackStrength.originalH)

theorem coupledLower_le (i : Fin 4) : coupledLower (ActualNineFeedback.coupledRow i) ≤
    ActualNineFeedback.coupledFeedback (ActualNineFeedback.coupledRow i) NineFeedbackStrength.originalH := by
  have ha := CoupledFiniteAssembly.aCoefficient_nonneg (ActualNineFeedback.coupledRow_geometry i)
  have hs : profileLower ≤ SigmaInnerProfile.d0Lower NineFeedbackStrength.originalH :=
    max_le SigmaInnerProfile.old_finiteLower_le elementaryLower_le
  have h := mul_le_mul_of_nonneg_left hs ha
  have hc := SigmaInnerProfile.coupledLower_le_original i
  unfold coupledLower SigmaInnerProfile.coupledLower at *
  linarith only [h,hc]
end
end SigmaPrimitiveCells
