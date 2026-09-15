import JointHMotherPayment

namespace Wu2008DoubleSieve.SignedTotalCorrelation
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure (a b s)
open FixedCoefficientHLowerEnclosure (c)
open Phase23 (alphaModel gModel modelBase CP)
open UnroundedPayments (j7Upper j8Upper j9Upper weightedJUpper)
noncomputable section

/-- Residuals of the original fixed log envelope, with no new approximation. -/
def e2 : ℝ := log 2-lowerLog 2
def e43 : ℝ := log (4/3)-lowerLog (4/3)
def e54 : ℝ := log (5/4)-lowerLog (5/4)
def d2 : ℝ := upperLog 2-lowerLog 2
def d43 : ℝ := upperLog (4/3)-lowerLog (4/3)
def d54 : ℝ := upperLog (5/4)-lowerLog (5/4)
def jTwo : ℝ := 100/9+8*SharpJBalance.ninthA

theorem base_residual_lower :
    modelBase+32*e2+132*e43+24*GConvexChord.C*e54 ≤ 24*alphaModel+8*wuLowerCoefficient (1/(2*b)) := by
  have hb := BaseRecurrenceLower.beta_real_lower
  have h3 := SharpLogRecurrence.log_lower (by norm_num : (1 : ℝ) ≤ 3/2)
  have hsplit := SharpJBalance.log_split_two (by norm_num : (0 : ℝ) < 3)
  have h43 := SharpLogRecurrence.log_lower (by norm_num : (1 : ℝ) ≤ 4/3)
  have h54 := SharpLogRecurrence.log_lower (by norm_num : (1 : ℝ) ≤ 5/4)
  have hb3 := SharpLogRecurrence.log_lower (by norm_num : (1 : ℝ) ≤ (78/25)/3)
  unfold alphaModel modelBase e2 e43 e54
  rw [Phase23.CP_difference (by norm_num) (by norm_num),
    BaseRecurrenceLower.P_difference 0 GConvexChord.C GConvexChord.m (by norm_num) (by norm_num)]
  rw [BaseRecurrenceLower.Q_difference (by norm_num) (by norm_num)] at hb
  norm_num [GConvexChord.m,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,
    b,truncatedSixthLowerBeta,SharpLogRecurrence.lowerLog] at hb h43 h54 hb3 ⊢
  norm_num [SharpLogRecurrence.lowerLog] at h3 hsplit
  linarith

theorem g_residual_upper :
    gModel ≤ GConvexChord.rationalG-88*(d43-e43)-16*GConvexChord.C*(d54-e54) := by
  unfold d43 e43 d54 e54
  change (8/VariableGIntegral.a)*(42823/151875)*log (VariableGIntegral.c 5/VariableGIntegral.a)+8*GConvexChord.endpoint+
    8*(VariableGIntegral.primitive VariableGIntegral.s-VariableGIntegral.primitive (VariableGIntegral.c 4))+8*log (6*VariableGIntegral.a/VariableGIntegral.s) ≤ GConvexChord.rationalG-88*((upperLog (4/3)-lowerLog (4/3))-(log (4/3)-lowerLog (4/3)))-16*GConvexChord.C*((upperLog (5/4)-lowerLog (5/4))-(log (5/4)-lowerLog (5/4)))
  rw [VariableGIntegral.endpoint]
  have h1 := log_upper (t := c 5/a)
    (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,a,truncatedSixthLowerAlpha])
  have h2 := log_upper (t := c 4/c 5)
    (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha])
  have h3 := log_upper (t := s/c 4)
    (by norm_num [s,c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h4 := log_upper (t := (4/3 : ℝ)) (by norm_num)
  have h5 := log_upper (t := 6*a/s)
    (by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h6 := log_upper (t := (5/4 : ℝ)) (by norm_num)
  unfold GConvexChord.rationalG GConvexChord.endpoint at *
  norm_num [GConvexChord.m,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,VariableGIntegral.logCoefficient,VariableGIntegral.linearCoefficient,a,truncatedSixthLowerAlpha, c,s,VariableGIntegral.c,VariableGIntegral.s,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerSigma] at h1 h2 h3 h4 h5 h6 ⊢
  linarith


theorem eighth_residual_upper : SeventhEighth.J8 ≤ j8Upper-(25/18)*(d2-e2) := by
  unfold d2 e2
  have h8 := SharpJBalance.J8_primitive_upper
  rw [SharpJBalance.log_split_four
    (by norm_num [SharpJBalance.a,SeventhEighth.alpha] : 0 < (1/3 : ℝ)/SharpJBalance.a)] at h8
  have h81 := log_upper (t := ((1/3)/SharpJBalance.a)/4)
    (by norm_num [SharpJBalance.a,SeventhEighth.alpha])
  have h82 := log_upper (t := (1-SharpJBalance.a)/(2/3))
    (by norm_num [SharpJBalance.a,SeventhEighth.alpha])
  have h83 := log_lower (t := 2-3*SharpJBalance.a)
    (by norm_num [SharpJBalance.a,SeventhEighth.alpha])
  have h2 := log_two_bounds.2
  norm_num [SharpJBalance.a,SeventhEighth.alpha,upperLog,lowerLog,j8Upper] at h8 h81 h82 h83 ⊢
  linarith

theorem ninth_residual_upper : J9 ≤ j9Upper-SharpJBalance.ninthA*(d2-e2) := by
  unfold d2 e2
  have h9 := SharpJBalance.J9_primitive_upper
  rw [SharpJBalance.log_split_two (by norm_num [SharpJBalance.b,SharpJBalance.s,
    SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2] :
    0 < SharpJBalance.s/SharpJBalance.b)] at h9
  have h91 := log_upper (t := (SharpJBalance.s/SharpJBalance.b)/2)
    (by norm_num [SharpJBalance.b,SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h92 := log_upper (t := (1-SharpJBalance.b)/(1-SharpJBalance.s))
    (by norm_num [SharpJBalance.b,SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h93 := log_lower (t := (1-SharpJBalance.s-SharpJBalance.b)/(1-2*SharpJBalance.s))
    (by norm_num [SharpJBalance.b,SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h2 := log_two_bounds.2
  norm_num [SharpJBalance.b,SharpJBalance.s,SeventhEighth.alpha,SeventhEighth.sigma,
    ninthProfileK2,SharpJBalance.ninthA,SharpJBalance.ninthB,SharpJBalance.ninthC,
    SharpJBalance.ninthD,upperLog,lowerLog,j9Upper] at h9 h91 h92 h93 ⊢
  linarith

/-- The log-two occurrence is shared by the original base and both negative J terms. -/
theorem weighted_j_residual_upper :
    16*SeventhEighth.J7+8*SeventhEighth.J8+8*J9 ≤ weightedJUpper-jTwo*(d2-e2) := by
  have h7 := UnroundedPayments.J7_le_j7Upper
  have h8 := eighth_residual_upper
  have h9 := ninth_residual_upper
  unfold weightedJUpper jTwo
  nlinarith only [h7,h8,h9]

def correlationGain : ℝ := 88*d43+16*GConvexChord.C*d54+jTwo*d2

/-- The complete old signed envelope, with shared endpoint logs paid only after collection. -/
theorem correlated_signed_lower :
    modelBase-GConvexChord.rationalG-weightedJUpper+correlationGain ≤
      24*wuLowerCoefficient (1/(2*a))-
        (SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s)+
        8*wuLowerCoefficient (1/(2*b))-
        (16*SeventhEighth.J7+8*SeventhEighth.J8+8*J9) := by
  have hb := base_residual_lower
  have hg := g_residual_upper
  have hj := weighted_j_residual_upper
  have hs := Phase23.shared_actual_lower
  have h2 : 0 ≤ e2 := sub_nonneg.mpr (log_lower (by norm_num))
  have h43 : 0 ≤ e43 := sub_nonneg.mpr (log_lower (by norm_num))
  have h54 : 0 ≤ e54 := sub_nonneg.mpr (log_lower (by norm_num))
  have hc := GConvexChord.chord_positive.2
  have hj2 : jTwo ≤ 32 := by
    norm_num [jTwo,SharpJBalance.ninthA,SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hprod := mul_nonneg (sub_nonneg.mpr hj2) h2
  have hcprod := mul_nonneg hc.le h54
  unfold correlationGain
  nlinarith only [hb,hg,hj,hs,h43,hprod,hcprod]

/-- Reassemble every original signed producer; no independent counting lower is added. -/
def kLower : ℝ := modelBase+UnroundedPayments.fifthRational+Phase25.newSixth+
  47/481250-GConvexChord.rationalG-weightedJUpper-Phase24.newFour+correlationGain

theorem complete_lower : kLower < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have h := correlated_signed_lower
  have hf := UnroundedPayments.fifthRational_lt_fifthPairFlin
  have h6 := Phase25.actual_sixth_ge_new
  have hi := Phase24.original_four_upper
  unfold kLower TruncatedElevenClassicalCountLower.classicalCoefficient
  linarith only [h,hf,h6,hi]

theorem gain_positive : 0 < correlationGain := by
  norm_num [correlationGain,d43,d54,d2,jTwo,upperLog,lowerLog,
    GConvexChord.C,GConvexChord.r4,GConvexChord.r5,SharpJBalance.ninthA,
    SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha]

theorem strict_improvement : Phase25.kLower < kLower := by
  have h := gain_positive
  unfold kLower Phase25.kLower
  linarith only [h]

def lowerCoefficient : ℝ := kLower/4+Phase20.fixedPsi+Phase18.g18+
  (2*BaseHGain.originalGain+fifthHGain/4)

theorem joint_actual_lower : lowerCoefficient < JointHMotherPayment.unroundedCoefficient := by
  rw [JointHMotherPayment.unrounded_coefficient_identity]
  have h := complete_lower
  have hp := Phase20.psi_payment_loss_nonneg
  unfold Phase20.psiPaymentLoss at hp
  unfold lowerCoefficient
  linarith only [h,hp]

theorem fixed_improvement_identity :
    lowerCoefficient = JointHMotherPayment.lowerCoefficient+correlationGain/4 := by
  unfold lowerCoefficient JointHMotherPayment.lowerCoefficient Phase25.lowerCoefficient
    kLower Phase25.kLower
  ring

/-- The unreplaced analytic residual is retained as well as the fixed gain. -/
def retainedResidual : ℝ := (32-jTwo)*e2+44*e43+8*GConvexChord.C*e54

theorem retainedResidual_nonneg : 0 ≤ retainedResidual := by
  have h2 : 0 ≤ e2 := sub_nonneg.mpr (log_lower (by norm_num))
  have h43 : 0 ≤ e43 := sub_nonneg.mpr (log_lower (by norm_num))
  have h54 : 0 ≤ e54 := sub_nonneg.mpr (log_lower (by norm_num))
  have hc := GConvexChord.chord_positive.2
  have hj2 : jTwo ≤ 32 := by
    norm_num [jTwo,SharpJBalance.ninthA,SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha]
  unfold retainedResidual
  exact add_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr hj2) h2)
    (mul_nonneg (by norm_num) h43)) (mul_nonneg (by positivity) h54)

theorem complete_residual_lower :
    kLower+retainedResidual < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := base_residual_lower
  have hg := g_residual_upper
  have hj := weighted_j_residual_upper
  have hs := Phase23.shared_actual_lower
  have hf := UnroundedPayments.fifthRational_lt_fifthPairFlin
  have h6 := Phase25.actual_sixth_ge_new
  have hi := Phase24.original_four_upper
  unfold kLower correlationGain retainedResidual TruncatedElevenClassicalCountLower.classicalCoefficient
  nlinarith only [hb,hg,hj,hs,hf,h6,hi]

theorem joint_actual_residual_lower :
    lowerCoefficient+retainedResidual/4 < JointHMotherPayment.unroundedCoefficient := by
  rw [JointHMotherPayment.unrounded_coefficient_identity]
  have h := complete_residual_lower
  have hp := Phase20.psi_payment_loss_nonneg
  unfold Phase20.psiPaymentLoss at hp
  unfold lowerCoefficient
  linarith only [h,hp]

theorem exact_gain : correlationGain =
    (13156657967868566329/211795262963746205625 : ℝ) := by
  norm_num [correlationGain,d43,d54,d2,jTwo,upperLog,lowerLog,
    GConvexChord.C,GConvexChord.r4,GConvexChord.r5,SharpJBalance.ninthA,
    SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha]

/-- A fixed non-infinitesimal improvement; this is not the target threshold claim. -/
theorem fixed_gain_gt_one_eightieth :
    JointHMotherPayment.lowerCoefficient+1/80 < lowerCoefficient := by
  rw [fixed_improvement_identity,exact_gain]
  linarith

#print axioms correlated_signed_lower
#print axioms complete_lower
#print axioms joint_actual_lower
#print axioms complete_residual_lower
#print axioms joint_actual_residual_lower
#print axioms exact_gain
#print axioms fixed_gain_gt_one_eightieth
end
end Wu2008DoubleSieve.SignedTotalCorrelation
