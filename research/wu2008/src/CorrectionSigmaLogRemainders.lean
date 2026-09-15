import CorrectionD0Remainders

noncomputable section
namespace CorrectionSigmaLog
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals
open SigmaInnerPaid SigmaSignedCells SigmaCorrectionFTC
open scoped Interval BigOperators

/-- The exact three original endpoint log errors; all coefficient signs are retained. -/
def endpointLogUnpaid (t : ℝ) : ℝ :=
  aCoeff t*(log ((t+2)/3)-RemainingHf.basicLower ((t+2)/3))+
  bCoeff t*(log ((t+1)/2)-RemainingHf.basicLower ((t+1)/2))+
  (-cCoeff t)*(RemainingHf.basicUpper ((2*t+2)/(t+3))-log ((2*t+2)/(t+3)))

theorem endpointLogUnpaid_nonneg {t : ℝ} (ht : 1 ≤ t) (ht3 : t ≤ 3) :
    0 ≤ endpointLogUnpaid t := by
  have ha := sub_nonneg.mpr (RemainingHf.basicLower_le (x := (t+2)/3) (by linarith))
  have hb := sub_nonneg.mpr (RemainingHf.basicLower_le (x := (t+1)/2) (by linarith))
  have hc := sub_nonneg.mpr (RemainingHf.le_basicUpper
    ((one_le_div (by linarith : 0<t+3)).mpr (by linarith : t+3 ≤ 2*t+2)))
  exact add_nonneg (add_nonneg (mul_nonneg (aCoeff_nonneg ht ht3) ha)
    (mul_nonneg (bCoeff_nonneg ht) hb)) (mul_nonneg (neg_nonneg.mpr (cCoeff_nonpos ht)) hc)

theorem kernel_balance (t : ℝ) : SigmaInnerEndpointRecovery.kernel t=
    endpointPaid t+innerCorrection t+endpointLogUnpaid t := by
  rw [kernel_collected]
  unfold endpointPaid innerCorrection lowerRemainder endpointLogUnpaid RemainingHf.basicUpper
  ring

theorem weight_balance (t : ℝ) : endpointLogUnpaid t/t=
    SigmaInnerProfile.weight t-SigmaInnerPaid.weight t-correctionWeight t := by
  unfold SigmaInnerProfile.weight SigmaInnerPaid.weight correctionWeight
  rw [kernel_balance]
  ring

def cellLogUnpaid (a b : ℝ) : ℝ := ∫ t in a..b,endpointLogUnpaid t/t

theorem cellLogUnpaid_nonneg {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    0 ≤ cellLogUnpaid a b := by
  apply intervalIntegral.integral_nonneg hab
  intro t ht
  exact div_nonneg (endpointLogUnpaid_nonneg (ha.trans ht.1) (ht.2.trans hb))
    (by linarith [ht.1])

/-- The remaining original outer integral is exact, not endpoint quadrature. -/
theorem cell_balance {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    SigmaInnerProfile.cellIntegral a b=
      fullPrimitive b-fullPrimitive a+cellLogUnpaid a b := by
  have h0 : IntervalIntegrable SigmaInnerProfile.weight volume a b :=
    (SigmaInnerProfile.weight_continuous (by linarith : 0<a) hab).intervalIntegrable
  have h1 : IntervalIntegrable SigmaInnerPaid.weight volume a b :=
    (SigmaInnerPaid.weight_continuous (by linarith : 0<a) hab).intervalIntegrable
  have h2 : IntervalIntegrable correctionWeight volume a b :=
    (correctionWeight_continuous (by linarith : 0<a) hab).intervalIntegrable
  have he : cellLogUnpaid a b=SigmaInnerProfile.cellIntegral a b-
      (SigmaInnerPaid.primitive b-SigmaInnerPaid.primitive a)-correctionMass a b := by
    unfold cellLogUnpaid
    simp_rw [weight_balance]
    rw [intervalIntegral.integral_sub (h0.sub h1) h2,intervalIntegral.integral_sub h0 h1,
      SigmaInnerPaid.weight_integral ha hab]
    rfl
  rw [fullCell_identity ha hab]
  unfold SigmaPrimitiveCells.cellMass
  linarith only [he]

def kernelNumeratorUnpaid : ℝ := ∑ k : Fin 9,NineFeedbackStrength.originalH k*
  cellLogUnpaid (upperLeft k) (upperNode k)

def endpointNumeratorUnpaid : ℝ := ∑ k : Fin 9,NineFeedbackStrength.originalH k*
  (fullPrimitive (upperNode k)-fullPrimitive (upperLeft k)-fullCellPaid (upperLeft k) (upperNode k))

theorem kernelNumeratorUnpaid_nonneg : 0 ≤ kernelNumeratorUnpaid := by
  apply Finset.sum_nonneg
  intro k _
  obtain ⟨ha,hab,hb⟩ := original_cell_bounds k
  exact mul_nonneg (CoupledIntegralRecovery.originalH_nonneg k) (cellLogUnpaid_nonneg ha hab hb)

theorem endpointNumeratorUnpaid_nonneg : 0 ≤ endpointNumeratorUnpaid := by
  apply Finset.sum_nonneg
  intro k _
  obtain ⟨ha,hab,_⟩ := original_cell_bounds k
  exact mul_nonneg (CoupledIntegralRecovery.originalH_nonneg k)
    (sub_nonneg.mpr (fullCellPaid_le ha hab))

theorem numerator_balance : SigmaInnerProfile.numerator NineFeedbackStrength.originalH=
    fullNumerator+endpointNumeratorUnpaid+kernelNumeratorUnpaid := by
  unfold SigmaInnerProfile.numerator fullNumerator endpointNumeratorUnpaid kernelNumeratorUnpaid
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  obtain ⟨ha,hab,_⟩ := original_cell_bounds k
  rw [cell_balance ha hab]
  ring

/-- The common-parent max cannot be subtracted without paying its exact numerator cost. -/
def maxCost : ℝ := CorrectionD0Joint.numerator-fullNumerator

theorem maxCost_nonneg : 0 ≤ maxCost := by
  have hd := sub_pos.mpr SigmaRemaining.d0Paid_lt_one
  have h : fullNumerator/(1-SigmaRemaining.d0Paid) ≤ CorrectionD0Joint.base :=
    (le_max_right _ _).trans (le_max_left _ _)
  exact sub_nonneg.mpr ((div_le_iff₀ hd).mp h)

theorem common_sigmaUnpaid_balance : CorrectionD0Joint.sigmaUnpaid=
    endpointNumeratorUnpaid+kernelNumeratorUnpaid-maxCost := by
  unfold CorrectionD0Joint.sigmaUnpaid maxCost
  rw [numerator_balance]
  ring

end CorrectionSigmaLog
