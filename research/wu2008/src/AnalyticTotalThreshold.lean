import SharedRationalPayment

namespace Wu2008DoubleSieve.AnalyticTotalThreshold
open Real ClassicalAnalyticLeaves
open FixedCoefficientUpperEnclosure (a b)
noncomputable section

/-- The original target, not the merely sufficient rational benchmark. -/
def target : ℝ := 8 * log (5000/4469)

/-- Retain the entire already proved fifth FTC endpoint. -/
def fifthEndpoint : ℝ :=
  2*SharpMassBalance.fifthDensity*(log b-log a)^2 +
    4*FifthClassicalShape.k*(b*(log b-log a)^2-(b-a)*(log b-log a))

/-- Retain the original sixth rational-kernel FTC endpoint, before log payment. -/
def sixthEndpoint : ℝ := 4*(Phase25.outerPrimitive b-Phase25.outerPrimitive a)

/-- This signed model retains the correlated real-log residual and shared integral. -/
def signedModel : ℝ := Phase23.modelBase-GConvexChord.rationalG-
  UnroundedPayments.weightedJUpper+SignedTotalCorrelation.correlationGain+
  SignedTotalCorrelation.retainedResidual+SharedRationalEnvelope.deltaShared

/-- The actual correlated block; no independent base and G estimates are added. -/
def signedActual : ℝ := 24*wuLowerCoefficient (1/(2*a))-
  (SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin FixedCoefficientUpperEnclosure.s)+
  8*wuLowerCoefficient (1/(2*b))-
  (16*SeventhEighth.J7+8*SeventhEighth.J8+8*J9)

theorem signedModel_le_actual : signedModel ≤ signedActual := by
  have hb := SignedTotalCorrelation.base_residual_lower
  have hg := SignedTotalCorrelation.g_residual_upper
  have hj := SignedTotalCorrelation.weighted_j_residual_upper
  have hs := SharedRationalPayment.shared_actual_lower
  unfold signedModel signedActual SignedTotalCorrelation.correlationGain
    SignedTotalCorrelation.retainedResidual
  nlinarith only [hb,hg,hj,hs]

theorem fifthEndpoint_le_actual : fifthEndpoint ≤ fifthPairFlin :=
  FifthClassicalShape.shape_integral_lower

theorem sixthEndpoint_le_actual : sixthEndpoint ≤ truncatedSixthLowerF6lin := by
  have h := Phase25.actual_sixth_ge_rationalInner
  rw [Phase25.outer_ftc] at h
  exact h

theorem newSixth_le_endpoint : Phase25.newSixth ≤ sixthEndpoint :=
  Phase25.newSixth_lower

/-- All original signs and the unit contribution are unchanged. -/
def classicalEndpoint : ℝ := signedModel+fifthEndpoint+sixthEndpoint+
  47/481250-Phase24.newFour

/-- No rational Psi payment: this is exactly the original HighSix window. -/
def coefficient : ℝ := classicalEndpoint/4+Phase20.rawPsi+Phase18.g18+
  (2*BaseHGain.originalGain+fifthHGain/4)

/-- Four actual model errors, not estimates of the size of Q. -/
def signedLoss : ℝ := signedActual-signedModel
def fifthLoss : ℝ := fifthPairFlin-fifthEndpoint
def sixthLoss : ℝ := truncatedSixthLowerF6lin-sixthEndpoint
def fourLoss : ℝ := Phase24.newFour-
  (8*FourRoughClosedMass.I10+8*FourRoughClosedMass.I11)

theorem losses_nonnegative : 0 ≤ signedLoss ∧ 0 ≤ fifthLoss ∧
    0 ≤ sixthLoss ∧ 0 ≤ fourLoss := by
  refine ⟨sub_nonneg.mpr signedModel_le_actual,
    sub_nonneg.mpr fifthEndpoint_le_actual,
    sub_nonneg.mpr sixthEndpoint_le_actual, ?_⟩
  exact sub_nonneg.mpr Phase24.original_four_upper

/-- The four distinct original signed-producer errors inside signedLoss. -/
def baseLoss : ℝ := 24*Phase23.alphaModel+8*wuLowerCoefficient (1/(2*b))-
  (Phase23.modelBase+32*SignedTotalCorrelation.e2+132*SignedTotalCorrelation.e43+
    24*GConvexChord.C*SignedTotalCorrelation.e54)
def gLoss : ℝ := GConvexChord.rationalG-
  88*(SignedTotalCorrelation.d43-SignedTotalCorrelation.e43)-
  16*GConvexChord.C*(SignedTotalCorrelation.d54-SignedTotalCorrelation.e54)-Phase23.gModel
def jLoss : ℝ := UnroundedPayments.weightedJUpper-
  SignedTotalCorrelation.jTwo*(SignedTotalCorrelation.d2-SignedTotalCorrelation.e2)-
  (16*SeventhEighth.J7+8*SeventhEighth.J8+8*J9)
def sharedLoss : ℝ := 24*wuLowerCoefficient (1/(2*a))-
  (SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin FixedCoefficientUpperEnclosure.s)-
  (24*Phase23.alphaModel-Phase23.gModel+SharedRationalEnvelope.deltaShared)

theorem signed_losses_nonnegative : 0 ≤ baseLoss ∧ 0 ≤ gLoss ∧
    0 ≤ jLoss ∧ 0 ≤ sharedLoss := by
  exact ⟨sub_nonneg.mpr SignedTotalCorrelation.base_residual_lower,
    sub_nonneg.mpr SignedTotalCorrelation.g_residual_upper,
    sub_nonneg.mpr SignedTotalCorrelation.weighted_j_residual_upper,
    sub_nonneg.mpr SharedRationalPayment.shared_actual_lower⟩

theorem signed_loss_identity : signedLoss = baseLoss+gLoss+jLoss+sharedLoss := by
  unfold signedLoss signedActual signedModel baseLoss gLoss jLoss sharedLoss
    SignedTotalCorrelation.correlationGain SignedTotalCorrelation.retainedResidual
  ring

/-- Every unpaid classical term survives in the exact difference. -/
theorem actual_gap_identity : JointHMotherPayment.unroundedCoefficient-coefficient =
    (signedLoss+fifthLoss+sixthLoss+fourLoss)/4 := by
  rw [JointHMotherPayment.unrounded_coefficient_identity]
  unfold coefficient classicalEndpoint signedLoss fifthLoss sixthLoss fourLoss signedActual
    TruncatedElevenClassicalCountLower.classicalCoefficient
  simp only [a,b,FixedCoefficientUpperEnclosure.s]
  ring

theorem coefficient_le_actual : coefficient ≤ JointHMotherPayment.unroundedCoefficient := by
  have h := losses_nonnegative
  have he := actual_gap_identity
  linarith only [h.1,h.2.1,h.2.2.1,h.2.2.2,he]

/-- The exact replacements relative to the accepted full-analytic certificate. -/
theorem retained_replacements_identity :
    coefficient-SharedRationalPayment.residualCoefficient =
      Phase20.psiPaymentLoss +
      (fifthEndpoint-FifthClassicalShape.payment)/4 +
      (sixthEndpoint-Phase25.newSixth)/4 := by
  unfold coefficient classicalEndpoint signedModel SharedRationalPayment.residualCoefficient
    FifthShapePayment.residualCoefficient FifthShapePayment.lowerCoefficient
    FifthShapePayment.kLower SignedTotalCorrelation.kLower FifthClassicalShape.payment
    Phase20.psiPaymentLoss
  ring

/-- A sufficient whole-expression comparison, with no new count consumer. -/
theorem sufficient_comparison (h : target < coefficient) :
    target < JointHMotherPayment.unroundedCoefficient :=
  h.trans_le coefficient_le_actual

/-- A necessary and sufficient comparison retaining every actual model error. -/
theorem exact_remaining_obligation :
    target < JointHMotherPayment.unroundedCoefficient ↔
      4*(target-coefficient) < signedLoss+fifthLoss+sixthLoss+fourLoss := by
  have he := actual_gap_identity
  constructor <;> intro h <;> linarith only [he,h]

/-- Restore Psi directly in the accepted certificate without expanding its domain. -/
theorem rawPsi_restored_strict :
    SharedRationalPayment.residualCoefficient+Phase20.psiPaymentLoss <
      JointHMotherPayment.unroundedCoefficient := by
  have h := SharedRationalPayment.complete_residual_lower
  rw [JointHMotherPayment.unrounded_coefficient_identity]
  unfold SharedRationalPayment.residualCoefficient FifthShapePayment.residualCoefficient
    FifthShapePayment.lowerCoefficient Phase20.psiPaymentLoss
  linarith only [h]

end
end Wu2008DoubleSieve.AnalyticTotalThreshold
