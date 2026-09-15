import JointEndpointPayment

namespace Wu2008DoubleSieve.JointLogTotalComparison
open Real SharpLogRecurrence TotalEndpointComparison
open FixedCoefficientUpperEnclosure (a b s)
noncomputable section

/-- The prescribed combination of the two original rational envelopes. -/
def V (x : ℝ) : ℝ := (3*upperLog x+2*lowerLog x)/5

theorem log_le_V {x : ℝ} (hx : 1 ≤ x) : log x ≤ V x := by
  have h := JointJLossStrength.envelope_error_comparison hx
  unfold V
  linarith only [h]

/-- Coefficients after collecting every shared, residual, fifth and sixth log. -/
def c2 : ℝ := A1+32-SignedTotalCorrelation.jTwo
def c43 : ℝ := A1+100
def c54 : ℝ := 8*GConvexChord.C
def cH : ℝ := -16*gap H
def cD : ℝ := 2*quad*FifthClassicalShape.ell+lin
def rH : ℝ := (H-2)/(H-3)

def logTotal : ℝ := c2*log 2-c43*log (4/3)+c54*log (5/4)-cH*log rH+
  cD*log (b/a)+4*(Phase25.kx*log Phase25.ratioz+
  Phase25.qb1*log (Phase25.ratiob/Phase25.ratioz)-
  Phase25.qm1*log (Phase25.ratioz/Phase25.ratiom)+
  Phase25.qp1*log (Phase25.ratiop/Phase25.ratioz))

def logPayment : ℝ := c2*lowerLog 2-c43*V (4/3)+c54*lowerLog (5/4)-cH*V rH+
  cD*lowerLog (b/a)+4*(Phase25.kx*lowerLog Phase25.ratioz+
  Phase25.qb1*lowerLog (Phase25.ratiob/Phase25.ratioz)-
  Phase25.qm1*V (Phase25.ratioz/Phase25.ratiom)+
  Phase25.qp1*lowerLog (Phase25.ratiop/Phase25.ratioz))

def rationalPart : ℝ := Phase23.modelBase-GConvexChord.rationalG-
  UnroundedPayments.weightedJUpper+SignedTotalCorrelation.correlationGain+rationalJoint+
  4*Phase25.endpointRational+47/481250-Phase24.newFour-quad*FifthClassicalShape.ell^2

def classicalPayment : ℝ := (rationalPart+logPayment)/4

def retainedExtra : ℝ := Phase20.rawPsi+Phase18.g18+
  (2*BaseHGain.originalGain+fifthHGain/4)

/-- The recovery product remains literal, and is spent exactly once. -/
def analyticCertificate : ℝ := classicalPayment+retainedExtra+JointJLossStrength.recovery/4

def fixedCertificate : ℝ := classicalPayment+Phase20.fixedPsi+Phase18.g18+
  (2*BaseHGain.originalGain+fifthHGain/4)+JointJLossStrength.fixedRecovery/4

macro "fixed_num" : tactic => `(tactic| norm_num [c2,c43,c54,cH,cD,rH,A1,H,gap,quad,lin,
  FifthClassicalShape.ell,FifthClassicalShape.k,FifthClassicalShape.c,FifthClassicalShape.f,
  FifthClassicalShape.q,SharpMassBalance.s0,SharpMassBalance.fifthDensity,
  SharpMassBalance.a,SharpMassBalance.b,lowerLog,upperLog,V,
  SignedTotalCorrelation.jTwo,SharpJBalance.ninthA,SharpJBalance.s,
  SeventhEighth.sigma,SeventhEighth.alpha,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,
  Phase25.ratioz,Phase25.ratiob,Phase25.ratiom,Phase25.ratiop,
  Phase25.polez,Phase25.poleb,Phase25.polem,Phase25.polep,
  Phase25.kx,Phase25.qb1,Phase25.qm1,Phase25.qp1,
  a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma])

theorem collected_sixth : sixthRest = Phase25.endpointRational+
    Phase25.kx*log Phase25.ratioz+
    Phase25.qb1*log (Phase25.ratiob/Phase25.ratioz)-
    Phase25.qm1*log (Phase25.ratioz/Phase25.ratiom)+
    Phase25.qp1*log (Phase25.ratiop/Phase25.ratioz) := by
  have nz : Phase25.ratioz ≠ 0 := by fixed_num
  have nb : Phase25.ratiob ≠ 0 := by fixed_num
  have nm : Phase25.ratiom ≠ 0 := by fixed_num
  have np : Phase25.ratiop ≠ 0 := by fixed_num
  rw [log_div nb nz,log_div nz nm,log_div np nz]
  unfold sixthRest
  have h := congrArg (fun t : ℝ => t*log Phase25.ratioz) Phase25.residue_sum
  nlinarith only [h]

/-- Exact collection, before replacing any remaining logarithm. -/
theorem complete_collection :
    TotalEndpointComparison.affineTotal = (rationalPart+logTotal)/4+retainedExtra := by
  have h := shared_residual_joint
  have hlog : log ((H-3)/(H-2)) = -log rH := by
    rw [← log_inv]
    congr 1
    fixed_num
  rw [hlog] at h
  unfold TotalEndpointComparison.affineTotal rest
  rw [← shared_ftc,collected_sixth]
  unfold rationalPart logTotal retainedExtra c2 c43 c54 cH cD D
  linarith only [h]

/-- The entire signed log packet is paid only after collection. -/
theorem logPayment_le_total : logPayment ≤ logTotal := by
  have h2 := mul_le_mul_of_nonneg_left (log_lower (by norm_num : (1:ℝ) ≤ 2))
    (show 0 ≤ c2 by fixed_num)
  have h43 := mul_le_mul_of_nonneg_left (log_le_V (by norm_num : (1:ℝ) ≤ 4/3))
    (show 0 ≤ c43 by fixed_num)
  have h54 := mul_le_mul_of_nonneg_left (log_lower (by norm_num : (1:ℝ) ≤ 5/4))
    (show 0 ≤ c54 by fixed_num)
  have hH := mul_le_mul_of_nonneg_left (log_le_V (show 1 ≤ rH by fixed_num))
    (show 0 ≤ cH by fixed_num)
  have hD := mul_le_mul_of_nonneg_left (log_lower (show 1 ≤ b/a by fixed_num))
    (show 0 ≤ cD by fixed_num)
  have hz := mul_le_mul_of_nonneg_left (log_lower (show 1 ≤ Phase25.ratioz by fixed_num))
    (show 0 ≤ Phase25.kx by fixed_num)
  have hb := mul_le_mul_of_nonneg_left
    (log_lower (show 1 ≤ Phase25.ratiob/Phase25.ratioz by fixed_num))
    (show 0 ≤ Phase25.qb1 by fixed_num)
  have hm := mul_le_mul_of_nonneg_left
    (log_le_V (show 1 ≤ Phase25.ratioz/Phase25.ratiom by fixed_num))
    (show 0 ≤ Phase25.qm1 by fixed_num)
  have hp := mul_le_mul_of_nonneg_left
    (log_lower (show 1 ≤ Phase25.ratiop/Phase25.ratioz by fixed_num))
    (show 0 ≤ Phase25.qp1 by fixed_num)
  unfold logPayment logTotal
  linarith only [h2,h43,h54,hH,hD,hz,hb,hm,hp]

theorem analyticCertificate_le_parent :
    analyticCertificate ≤ JointEndpointPayment.analyticLower := by
  unfold analyticCertificate JointEndpointPayment.analyticLower classicalPayment
  rw [complete_collection]
  linarith only [logPayment_le_total]

theorem analyticCertificate_lt_actual :
    analyticCertificate < JointHMotherPayment.unroundedCoefficient :=
  analyticCertificate_le_parent.trans_lt JointEndpointPayment.analyticLower_lt_actual

theorem fixedCertificate_le_analytic : fixedCertificate ≤ analyticCertificate := by
  have hp := Phase20.psi_payment_loss_nonneg
  have hj := JointJLossStrength.fixedRecovery_le_recovery
  unfold fixedCertificate analyticCertificate retainedExtra Phase20.psiPaymentLoss at *
  linarith only [hp,hj]

theorem fixedCertificate_lt_actual :
    fixedCertificate < JointHMotherPayment.unroundedCoefficient :=
  fixedCertificate_le_analytic.trans_lt analyticCertificate_lt_actual

/-- Exact nonnegative remainder; no target inequality is assumed. -/
def logRemainder : ℝ := (logTotal-logPayment)/4

theorem logRemainder_nonnegative : 0 ≤ logRemainder := by
  unfold logRemainder
  linarith only [logPayment_le_total]

theorem parent_exact_remainder :
    JointEndpointPayment.analyticLower = fixedCertificate+logRemainder+
      Phase20.psiPaymentLoss+(JointJLossStrength.recovery-JointJLossStrength.fixedRecovery)/4 := by
  unfold JointEndpointPayment.analyticLower
  rw [complete_collection]
  unfold fixedCertificate classicalPayment logRemainder retainedExtra Phase20.psiPaymentLoss
  ring

/-- Exact fixed total, retaining the original g18 separately. -/
def rationalTotal : ℝ := (93659430110705513357171650652119857927323371947843174795721599594191220034328633954101531603744011511272125561829536264879440499090854259031869777008018050009770568688131865949949491713752255898374400643366721928570811940362212354886070669905074206484604749019639280991609089510014174588546113/123839735061825490439251750561304259852907794318908610959950254266406351073248621917025650999420793684267454862872003827056733690407592203738501871432025302712907445246784053753902652760573765487141560345012648079809547821482827999296743694565752482390227210343873527540971466657016411000000000 : ℝ)
def rationalDeficit : ℝ := (330982736544448927529996090543192321446341329806040439718379005096092080078921491709381753998914217017684574640151965223685449144517484544352426186255989047474615951121661436337386107725896690627989430700449924233146949216107354275561718370883807836696785547073445306868727327959711332036119564310846319/2332663520567536754461128909458249601735957132248213024861358187542693731609529336311026934438561571382499575564545167633269268261835888414549384217644234068617410992894173811287449056933847783487437107063046861362352393626707486306747996474514978905726314140989134268830371358258837293826229707000000000 : ℝ)

theorem fixedCertificate_exact : fixedCertificate = rationalTotal+Phase18.g18 := by
  unfold fixedCertificate classicalPayment rationalPart logPayment rationalTotal
  norm_num [Phase23.modelBase,GConvexChord.rationalG,VariableGIntegral.logCoefficient,
    VariableGIntegral.linearCoefficient,VariableGIntegral.a,VariableGIntegral.s,
    VariableGIntegral.c,SharpSingleBalance.c,SharpSingleBalance.a,GConvexChord.m,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,
    UnroundedPayments.weightedJUpper,UnroundedPayments.j7Upper,UnroundedPayments.j8Upper,
    UnroundedPayments.j9Upper,SignedTotalCorrelation.correlationGain,
    SignedTotalCorrelation.d2,SignedTotalCorrelation.d43,SignedTotalCorrelation.d54,
    rationalJoint,rationalShared,A2,A3,Phase25.endpointRational,
    Phase24.newFour,Phase24.A,Phase24.c,FourLogAffine.w,FourLogAffine.l,FourLogAffine.u,
    FourRoughClosedMass.alpha,FourRoughClosedMass.beta,FourRoughClosedMass.lam,
    truncatedSixthLowerLambda,Phase20.fixedPsi,BaseHGain.originalGain,fifthHGain,fifthHSeed,
    JointJLossStrength.fixedRecovery,JointJLossStrength.massPayment,SharpJBalance.b,
    ninthProfileK2,c2,c43,c54,cH,cD,rH,A1,H,gap,quad,lin,
    FifthClassicalShape.ell,FifthClassicalShape.k,FifthClassicalShape.c,FifthClassicalShape.f,
    FifthClassicalShape.q,SharpMassBalance.s0,SharpMassBalance.fifthDensity,
    SharpMassBalance.a,SharpMassBalance.b,lowerLog,upperLog,V,
    SignedTotalCorrelation.jTwo,SharpJBalance.ninthA,SharpJBalance.s,
    SeventhEighth.sigma,SeventhEighth.alpha,
    Phase25.ratioz,Phase25.ratiob,Phase25.ratiom,Phase25.ratiop,
    Phase25.polez,Phase25.poleb,Phase25.polem,Phase25.polep,
    Phase25.kx,Phase25.qb1,Phase25.qm1,Phase25.qp1,
    a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma]
  ring

theorem rationalDeficit_exact :
    8*V (5000/4469)-rationalTotal = rationalDeficit := by
  norm_num [V,upperLog,lowerLog,rationalTotal,rationalDeficit]

theorem rationalDeficit_positive : 0 < rationalDeficit := by
  norm_num [rationalDeficit]

/-- This is the target envelope slack, not an extra Taylor remainder. -/
def targetSlack : ℝ := 8*(V (5000/4469)-log (5000/4469))

theorem targetSlack_nonnegative : 0 ≤ targetSlack := by
  have h := log_le_V (by norm_num : (1:ℝ) ≤ 5000/4469)
  unfold targetSlack
  linarith only [h]

/-- Full exact unresolved amount: a fixed rational debit and all genuine recoveries.
The positive debit does not give an upper bound on the actual coefficient. -/
theorem exact_target_parent_difference :
    AnalyticTotalThreshold.target-JointEndpointPayment.analyticLower =
      rationalDeficit-Phase18.g18-Phase20.psiPaymentLoss-logRemainder-
      (JointJLossStrength.recovery-JointJLossStrength.fixedRecovery)/4-targetSlack := by
  rw [parent_exact_remainder,fixedCertificate_exact,← rationalDeficit_exact]
  unfold AnalyticTotalThreshold.target targetSlack
  ring

/-- Restoring the original endpoint square gives the corresponding full-C remainder. -/
theorem exact_target_full_coefficient_difference :
    AnalyticTotalThreshold.target-(AnalyticTotalThreshold.coefficient+JointJLossStrength.recovery/4) =
      rationalDeficit-Phase18.g18-Phase20.psiPaymentLoss-logRemainder-
      (JointJLossStrength.recovery-JointJLossStrength.fixedRecovery)/4-targetSlack-
      quad/4*(D-FifthClassicalShape.ell)^2 := by
  have h := JointEndpointPayment.exact_square_gap
  have he := exact_target_parent_difference
  linarith only [h,he]

/-- A magnitude diagnostic of the fixed rational part only, not of Q. -/
theorem rational_magnitude : rationalTotal < 4/5 ∧ 1/10 < rationalDeficit := by
  norm_num [rationalTotal,rationalDeficit]

/-- Every surviving logarithmic slack, with its verified paying sign. -/
theorem logRemainder_expansion : 4*logRemainder =
    c2*(log 2-lowerLog 2)+c43*(V (4/3)-log (4/3))+
    c54*(log (5/4)-lowerLog (5/4))+cH*(V rH-log rH)+
    cD*(log (b/a)-lowerLog (b/a))+
    4*(Phase25.kx*(log Phase25.ratioz-lowerLog Phase25.ratioz)+
      Phase25.qb1*(log (Phase25.ratiob/Phase25.ratioz)-lowerLog (Phase25.ratiob/Phase25.ratioz))+
      Phase25.qm1*(V (Phase25.ratioz/Phase25.ratiom)-log (Phase25.ratioz/Phase25.ratiom))+
      Phase25.qp1*(log (Phase25.ratiop/Phase25.ratioz)-lowerLog (Phase25.ratiop/Phase25.ratioz))) := by
  unfold logRemainder logTotal logPayment
  ring

end
end Wu2008DoubleSieve.JointLogTotalComparison
