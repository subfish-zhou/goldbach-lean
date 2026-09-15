import SigmaSignedCellsPayment
namespace SigmaSignedCells
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment
open scoped Interval BigOperators
noncomputable section

def numerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9,z k*cellPaid (upperLeft k) (upperNode k)

theorem numerator_le {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    numerator z ≤ SigmaPrimitiveCells.numerator z := by
  apply Finset.sum_le_sum
  intro k _
  have hb := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he] at hb
  exact mul_le_mul_of_nonneg_left (cellPaid_le hb.1 hb.2.1) (hz k)

def finiteLower : ℝ := numerator NineFeedbackStrength.originalH/(1-SigmaRemaining.d0Paid)

theorem finiteLower_le : finiteLower ≤ SigmaPrimitiveCells.elementaryLower :=
  div_le_div_of_nonneg_right (numerator_le CoupledIntegralRecovery.originalH_nonneg)
    (sub_pos.mpr SigmaRemaining.d0Paid_lt_one).le

def profileLower : ℝ := max (SigmaRemaining.finiteLower NineFeedbackStrength.originalH) finiteLower

theorem profileLower_le_primitive : profileLower ≤ SigmaPrimitiveCells.profileLower :=
  max_le_max le_rfl finiteLower_le

theorem profileLower_le : profileLower ≤ aProfile (nineProfile NineFeedbackStrength.originalH) :=
  profileLower_le_primitive.trans SigmaPrimitiveCells.profileLower_le

theorem profileLower_pos : 0<profileLower :=
  SigmaRemaining.original_finiteLower_pos.trans_le (le_max_left _ _)

/-- Original full E/three J/middle/density expression; only the shared sigma is replaced. -/
def coupledLower (p : Wu2008DoubleSieve.SecondFunctionalParameters) : ℝ :=
  SigmaRemaining.coupledLower p+CoupledFiniteAssembly.aCoefficient p*
    (profileLower-SigmaRemaining.finiteLower NineFeedbackStrength.originalH)

theorem coupledLower_le (i : Fin 4) : coupledLower (ActualNineFeedback.coupledRow i) ≤
    ActualNineFeedback.coupledFeedback (ActualNineFeedback.coupledRow i) NineFeedbackStrength.originalH := by
  have hm := mul_le_mul_of_nonneg_left profileLower_le_primitive
    (CoupledFiniteAssembly.aCoefficient_nonneg (ActualNineFeedback.coupledRow_geometry i))
  have hc := SigmaPrimitiveCells.coupledLower_le i
  unfold coupledLower SigmaPrimitiveCells.coupledLower at *
  linarith only [hm,hc]
end
end SigmaSignedCells
