import ExactWeightTripleEnclosure

namespace Wu2008DoubleSieve.GlobalSignedActualComparison
open Real SharpLogRecurrence JointLogTotalComparison TotalEndpointComparison
open FixedCoefficientUpperEnclosure (a b s)
open ClassicalAnalyticLeaves
noncomputable section

/-- All recovery intermediates cancel before any inequality is applied. -/
theorem cancelled_actual_identity :
    JointHMotherPayment.unroundedCoefficient =
      (rationalPart+logTotal+quad*(D-FifthClassicalShape.ell)^2+
       JointSharedTightEnclosure.triple+AnalyticTotalThreshold.jLoss+
       (fifthPairFlin-AnalyticTotalThreshold.fifthEndpoint)+
       (truncatedSixthLowerF6lin-AnalyticTotalThreshold.sixthEndpoint)+
       AnalyticTotalThreshold.fourLoss)/4+retainedExtra := by
  have h := AnalyticTotalThreshold.actual_gap_identity
  rw [AnalyticTotalThreshold.signed_loss_identity] at h
  have hs := JointEndpointPayment.exact_square_gap
  have hc := complete_collection
  unfold JointEndpointPayment.analyticLower at hs
  unfold JointSharedTightEnclosure.triple AnalyticTotalThreshold.fifthLoss
    AnalyticTotalThreshold.sixthLoss at *
  linarith only [h,hs,hc]

def jLower (f : ℝ → ℝ) : ℝ :=
  16*(JCorrelatedResidualTight.C 1*(f ((1/3)/SharpJBalance.s)+f ((1-SharpJBalance.s)/(2/3)))+
    JCorrelatedResidualTight.R 1 3 SharpJBalance.s (1/3))+
  8*(JCorrelatedResidualTight.C (1/3)*(2*(f (4/3)+f (3/2))+f (JCubicPrimitive.crossRatio SharpJBalance.a (1/3)/4))+
    JCorrelatedResidualTight.R (1/3) 1 SharpJBalance.a (1/3))+
  8*(JCorrelatedResidualTight.C (1-2*SharpJBalance.s)*
    (f (4/3)+f (3/2)+f ((SharpJBalance.s/SharpJBalance.b)/2)+f ((1-SharpJBalance.b)/(1-SharpJBalance.s)))+
    JCorrelatedResidualTight.R (1-2*SharpJBalance.s) 1 SharpJBalance.b SharpJBalance.s)

theorem log_two : log (2:ℝ) = log (4/3)+log (3/2) := by
  rw [← log_mul (by norm_num : (4/3:ℝ) ≠ 0) (by norm_num : (3/2:ℝ) ≠ 0)]
  norm_num

theorem j_lower_identity : JFourRemainingMagnitude.jLowerReal = jLower log := by
  have hs0 : 0 < SharpJBalance.s := by norm_num [SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hs1 : SharpJBalance.s < 1 := by norm_num [SharpJBalance.s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hb0 : 0 < SharpJBalance.b := by norm_num [SharpJBalance.b,ninthProfileK2]
  have hb1 : SharpJBalance.b < 1 := by norm_num [SharpJBalance.b,ninthProfileK2]
  unfold JFourRemainingMagnitude.jLowerReal JCubicActualMass.fullMass
  rw [JCorrelatedResidualTight.cross_log hs0 (by norm_num : (0:ℝ)<1/3) hs1 (by norm_num),
    SharpJBalance.log_split_four (by norm_num [JCubicPrimitive.crossRatio,SharpJBalance.a,SeventhEighth.alpha] : 0 < JCubicPrimitive.crossRatio SharpJBalance.a (1/3)),
    JCorrelatedResidualTight.cross_log hb0 hs0 hb1 hs1,
    SharpJBalance.log_split_two (div_pos hs0 hb0),log_two]
  unfold jLower JCorrelatedResidualTight.C JCorrelatedResidualTight.R
  norm_num
  ring

def base (f : ℝ → ℝ) : ℝ :=
  32*(f (3/2)-lowerLog (3/2))+16*(f (26/25)-lowerLog (26/25))+8/12500

def mainLogs (f : ℝ → ℝ) : ℝ :=
  c2*(f (4/3)+f (3/2))-c43*f (4/3)+c54*f (5/4)-cH*f rH+
  cD*f (b/a)+4*(Phase25.kx*f Phase25.ratioz+
  Phase25.qb1*f (Phase25.ratiob/Phase25.ratioz)-
  Phase25.qm1*f (Phase25.ratioz/Phase25.ratiom)+
  Phase25.qp1*f (Phase25.ratiop/Phase25.ratioz))

/-- The complete global endpoint packet; all equal logarithms are still real. -/
def packet (f : ℝ → ℝ) : ℝ :=
  mainLogs f+quad*(f (b/a)-FifthClassicalShape.ell)^2+
  base f+ExactWeightTripleEnclosure.upperEnvelope f f+
  UnroundedPayments.weightedJUpper-SignedTotalCorrelation.jTwo*(upperLog 2-(f (4/3)+f (3/2)))-jLower f+
  2*(FifthLogTotalMagnitude.cap/a)*(f (b/a))^2-
  (2*SharpMassBalance.fifthDensity*(f (b/a))^2+
    4*FifthClassicalShape.k*(b*(f (b/a))^2-(b-a)*f (b/a)))

def upperReal : ℝ :=
  (rationalPart+packet log+FifthActualIntegralRecovery.recurrenceCap+
    SixthFullRationalEnclosure.payment+1/100000+
    Phase24.newFour-FourTrueLowerTight.actualLower)/4+retainedExtra

theorem actual_upper_real : JointHMotherPayment.unroundedCoefficient < upperReal := by
  have hw := ExactWeightTripleEnclosure.window_payments
  have hb := BaseGSharedActualRecovery.base_exact
  have hbeta := HighSharedKernelMagnitude.beta_bound
  have hg := BaseGSharedActualRecovery.g_exact
  have he := ExactWeightTripleEnclosure.upper_joint_identity
  have ht : JointSharedTightEnclosure.triple ≤ base log+
      ExactWeightTripleEnclosure.upperEnvelope log log := by
    unfold JointSharedTightEnclosure.triple
    rw [BaseGSharedActualRecovery.shared_exact]
    unfold base BaseGSharedActualRecovery.baseLogRemainder at *
    linarith only [hw.2.1,hw.2.2.2.1,hw.2.2.2.2,hb,hbeta,hg,he]
  have hj := JFourRemainingMagnitude.j_remaining_real_interval.2
  unfold JFourRemainingMagnitude.jRemaining JFourRemainingMagnitude.jCapReal at hj
  rw [j_lower_identity] at hj
  have h5 := FifthLogTotalMagnitude.integral_bounds.2
  have e5 := FifthActualIntegralRecovery.integral_distance.2
  have h6 := SixthFullRationalEnclosure.sixth_log_loss_enclosure.2
  have e6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.2
  have h4 := FourTrueLowerTight.actual_four_lower
  rw [cancelled_actual_identity]
  unfold upperReal packet mainLogs logTotal D AnalyticTotalThreshold.fourLoss
    AnalyticTotalThreshold.fifthEndpoint FifthLogTotalMagnitude.endpoint at *
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])] at h5
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])]
  rw [log_two]
  unfold SignedTotalCorrelation.d2 SignedTotalCorrelation.e2 at hj
  rw [log_two] at hj
  linarith only [ht,hj,h5,e5,h6,e6,h4]

macro "global_num" : tactic => `(tactic| norm_num [packet,mainLogs,base,jLower,JCorrelatedResidualTight.C,JCorrelatedResidualTight.R,JCubicPrimitive.rationalPart,JCubicPrimitive.crossRatio,ExactWeightTripleEnclosure.upperEnvelope,FifthLogTotalMagnitude.cap,FifthLogTotalMagnitude.hi,SharpJBalance.a,SharpJBalance.b,ninthProfileK2,c2,c43,c54,cH,cD,rH,A1,H,gap,quad,lin,
  FifthClassicalShape.ell,FifthClassicalShape.k,FifthClassicalShape.c,FifthClassicalShape.f,
  FifthClassicalShape.q,SharpMassBalance.s0,SharpMassBalance.fifthDensity,
  SharpMassBalance.a,SharpMassBalance.b,lowerLog,upperLog,V,
  SignedTotalCorrelation.jTwo,SharpJBalance.ninthA,SharpJBalance.s,
  SeventhEighth.sigma,SeventhEighth.alpha,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,
  Phase25.ratioz,Phase25.ratiob,Phase25.ratiom,Phase25.ratiop,
  Phase25.polez,Phase25.poleb,Phase25.polem,Phase25.polep,
  Phase25.kx,Phase25.qb1,Phase25.qm1,Phase25.qp1,
  a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma])

/-- One global sign collection, including the quadratic fifth endpoint. -/
def collected (L H : ℝ → ℝ) : ℝ :=
  (-16048621261886/189276975423)*L (4/3)+
  (32773647822399025736000/270937759807703592009)*H (3/2)+
  (943083088/114604875)*H (5/4)+
  (-2026091339037811711/77297510682000000)*L (727/527)+
  (12963658609426086898463268417154149083835937/982672734630224359211166378158240922977124)*H (1327/824)+
  (12963658609426086898463268417154149083835937/982672734630224359211166378158240922977124)*H (116081/103506)+
  (45711723750549248/1247524545012993)*H (6466668/6152293)+
  (-23526084706383522589366104523783786496/3729428911866529810567814389353)*L (4315543337/4281905212)+
  (47281093382566382680686050047210345/20476837392276624656401340676)*H (3728148112/3694509987)+
  (16)*H (26/25)+
  (-857478224/28940625)*L (327/200)+
  (-49368190687/1528065000)*L (527/327)+
  (-8)*L (1200/727)+
  (907616/3472875)*H (1127/1000)+
  (-128/3)*L (2654/2181)+
  (-128/3)*L (5781/5308)+
  (-448/81)*L (1227/800)+
  (-18056918400/2336752783)*L (74881/66350)+
  (-18056918400/2336752783)*L (240187/198481)+
  (6140336124508242059/827319551135595000)*(H (1327/824))^2

theorem collection (f : ℝ → ℝ) : packet f = packet (fun _ => 0)+collected f f := by
  unfold collected
  global_num
  ring

theorem collected_payment : collected log log ≤ collected lowerLog V := by
  have h0 := log_lower (by norm_num : (1:ℝ) ≤ 4/3)
  have h1 := log_le_V (by norm_num : (1:ℝ) ≤ 3/2)
  have h2 := log_le_V (by norm_num : (1:ℝ) ≤ 5/4)
  have h3 := log_lower (by norm_num : (1:ℝ) ≤ 727/527)
  have h4 := log_le_V (by norm_num : (1:ℝ) ≤ 1327/824)
  have h5 := log_le_V (by norm_num : (1:ℝ) ≤ 116081/103506)
  have h6 := log_le_V (by norm_num : (1:ℝ) ≤ 6466668/6152293)
  have h7 := log_lower (by norm_num : (1:ℝ) ≤ 4315543337/4281905212)
  have h8 := log_le_V (by norm_num : (1:ℝ) ≤ 3728148112/3694509987)
  have h9 := log_le_V (by norm_num : (1:ℝ) ≤ 26/25)
  have h10 := log_lower (by norm_num : (1:ℝ) ≤ 327/200)
  have h11 := log_lower (by norm_num : (1:ℝ) ≤ 527/327)
  have h12 := log_lower (by norm_num : (1:ℝ) ≤ 1200/727)
  have h13 := log_le_V (by norm_num : (1:ℝ) ≤ 1127/1000)
  have h14 := log_lower (by norm_num : (1:ℝ) ≤ 2654/2181)
  have h15 := log_lower (by norm_num : (1:ℝ) ≤ 5781/5308)
  have h16 := log_lower (by norm_num : (1:ℝ) ≤ 1227/800)
  have h17 := log_lower (by norm_num : (1:ℝ) ≤ 74881/66350)
  have h18 := log_lower (by norm_num : (1:ℝ) ≤ 240187/198481)
  have hn : 0 ≤ log (1327/824:ℝ) := log_nonneg (by norm_num)
  have hs := pow_le_pow_left₀ hn h4 2
  unfold collected
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,hs]

/-- Exact rational endpoint. Psi and g18 keep their genuine upper directions. -/
def upperRational : ℝ := rationalTotal+
  (packet (fun _ => 0)+collected lowerLog V-logPayment-JointJLossStrength.fixedRecovery+
    FifthActualIntegralRecovery.recurrenceCap+SixthFullRationalEnclosure.payment+1/100000+
    Phase24.newFour-FourTrueLowerTight.actualLower)/4+
  (328543353599/72210108813375-Phase20.fixedPsi)+354/1000000

theorem actual_upper : JointHMotherPayment.unroundedCoefficient < upperRational := by
  have hr := fixedCertificate_exact
  unfold fixedCertificate classicalPayment at hr
  have hp := PsiG18Strength.psi_loss_upper
  have hg := PsiG18Strength.g18_bounds.2
  have hc := collected_payment
  have hu := actual_upper_real
  unfold upperReal at hu
  rw [collection] at hu
  unfold upperRational retainedExtra Phase20.psiPaymentLoss at *
  linarith only [hr,hp,hg,hc,hu]

/-- Exact unpaid remainder of this globally correlated upper endpoint. -/
def upperRemainder : ℝ := upperRational-8*lowerLog (5000/4469)

macro "endpoint_num" : tactic => `(tactic| norm_num [FourTrueLowerTight.actual_lower_exact,FifthActualIntegralRecovery.recurrenceCap_exact.1,SixthFullRationalEnclosure.payment_rational,upperRational,upperRemainder,rationalTotal,collected,logPayment,UnroundedPayments.weightedJUpper,UnroundedPayments.j7Upper,UnroundedPayments.j8Upper,UnroundedPayments.j9Upper,JointJLossStrength.fixedRecovery,JointJLossStrength.massPayment,Phase24.newFour,Phase24.exactMass,Phase24.A,Phase24.c,FourLogAffine.w,FourLogAffine.l,FourLogAffine.u,FourRoughClosedMass.alpha,FourRoughClosedMass.beta,FourRoughClosedMass.lam,truncatedSixthLowerLambda,Phase20.fixedPsi,packet,mainLogs,base,jLower,JCorrelatedResidualTight.C,JCorrelatedResidualTight.R,JCubicPrimitive.rationalPart,JCubicPrimitive.crossRatio,ExactWeightTripleEnclosure.upperEnvelope,FifthLogTotalMagnitude.cap,FifthLogTotalMagnitude.hi,SharpJBalance.a,SharpJBalance.b,ninthProfileK2,c2,c43,c54,cH,cD,rH,A1,H,gap,quad,lin,
  FifthClassicalShape.ell,FifthClassicalShape.k,FifthClassicalShape.c,FifthClassicalShape.f,
  FifthClassicalShape.q,SharpMassBalance.s0,SharpMassBalance.fifthDensity,
  SharpMassBalance.a,SharpMassBalance.b,lowerLog,upperLog,V,
  SignedTotalCorrelation.jTwo,SharpJBalance.ninthA,SharpJBalance.s,
  SeventhEighth.sigma,SeventhEighth.alpha,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,
  Phase25.ratioz,Phase25.ratiob,Phase25.ratiom,Phase25.ratiop,
  Phase25.polez,Phase25.poleb,Phase25.polem,Phase25.polep,
  Phase25.kx,Phase25.qb1,Phase25.qm1,Phase25.qp1,
  a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma])

/-- The opposite complete endpoint, not a sum of independently rounded losses. -/
def lowerPacket (f : ℝ → ℝ) : ℝ :=
  mainLogs f+quad*(f (b/a)-FifthClassicalShape.ell)^2+
  ExactWeightTripleEnclosure.lowerEnvelope f f+JointJLossStrength.fixedRecovery+
  2*(FifthLogTotalMagnitude.f0/a)*(f (b/a))^2+
  4*(FifthLogTotalMagnitude.slope/a^2)*(b*(f (b/a))^2-(b-a)*f (b/a))-
  (2*SharpMassBalance.fifthDensity*(f (b/a))^2+
    4*FifthClassicalShape.k*(b*(f (b/a))^2-(b-a)*f (b/a)))+
  FourActualCapRecovery.recovery

def lowerReal : ℝ := (rationalPart+lowerPacket log)/4+retainedExtra

theorem lower_real_actual : lowerReal ≤ JointHMotherPayment.unroundedCoefficient := by
  have hw := ExactWeightTripleEnclosure.window_payments
  have hn := AnalyticTotalThreshold.signed_losses_nonnegative.1
  have hlow := BaseGSharedActualRecovery.low_nonnegative
  have hg := BaseGSharedActualRecovery.g_exact
  have he := ExactWeightTripleEnclosure.lower_joint_identity
  have ht : ExactWeightTripleEnclosure.lowerEnvelope log log ≤ JointSharedTightEnclosure.triple := by
    unfold JointSharedTightEnclosure.triple
    rw [BaseGSharedActualRecovery.shared_exact]
    linarith only [hw.1,hw.2.2.1,hn,hlow,hg,he]
  have hj := JointJLossStrength.actual_jLoss_lower
  have hjf := JointJLossStrength.fixedRecovery_le_recovery
  have h5 := FifthLogTotalMagnitude.integral_bounds.1
  have e5 := FifthActualIntegralRecovery.integral_distance.1
  have h6 := AnalyticTotalThreshold.losses_nonnegative.2.2.1
  have h4 := FourActualCapRecovery.actual_fourLoss_lower
  rw [cancelled_actual_identity]
  unfold lowerReal lowerPacket mainLogs logTotal D AnalyticTotalThreshold.sixthLoss
    AnalyticTotalThreshold.fifthEndpoint FifthLogTotalMagnitude.endpoint at *
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])] at h5
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])]
  rw [log_two]
  linarith only [ht,hj,hjf,h5,e5,h6,h4]

macro "lower_num" : tactic => `(tactic| norm_num [lowerPacket,ExactWeightTripleEnclosure.lowerEnvelope,FifthLogTotalMagnitude.f0,FifthLogTotalMagnitude.slope,FifthLogTotalMagnitude.lo,packet,mainLogs,base,jLower,JCorrelatedResidualTight.C,JCorrelatedResidualTight.R,JCubicPrimitive.rationalPart,JCubicPrimitive.crossRatio,ExactWeightTripleEnclosure.upperEnvelope,FifthLogTotalMagnitude.cap,FifthLogTotalMagnitude.hi,SharpJBalance.a,SharpJBalance.b,ninthProfileK2,c2,c43,c54,cH,cD,rH,A1,H,gap,quad,lin,
  FifthClassicalShape.ell,FifthClassicalShape.k,FifthClassicalShape.c,FifthClassicalShape.f,
  FifthClassicalShape.q,SharpMassBalance.s0,SharpMassBalance.fifthDensity,
  SharpMassBalance.a,SharpMassBalance.b,lowerLog,upperLog,V,
  SignedTotalCorrelation.jTwo,SharpJBalance.ninthA,SharpJBalance.s,
  SeventhEighth.sigma,SeventhEighth.alpha,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,
  Phase25.ratioz,Phase25.ratiob,Phase25.ratiom,Phase25.ratiop,
  Phase25.polez,Phase25.poleb,Phase25.polem,Phase25.polep,
  Phase25.kx,Phase25.qb1,Phase25.qm1,Phase25.qp1,
  a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma])

def lowerCollected (L H : ℝ → ℝ) : ℝ :=
  (-1455039607096/16731295047)*H (4/3)+
  (2126444395638171118684/23949767733688448001)*L (3/2)+
  (19588418/9646875)*L (5/4)+
  (-3577926257123/107357653725)*H (727/527)+
  (365398004238584479892646492386144279429431651602901425776353420683374723/28866867222069965312816790192096006285293922566262394302161692882477740)*L (1327/824)+
  (12963658609426086898463268417154149083835937/982672734630224359211166378158240922977124)*L (116081/103506)+
  (45711723750549248/1247524545012993)*L (6466668/6152293)+
  (-23526084706383522589366104523783786496/3729428911866529810567814389353)*H (4315543337/4281905212)+
  (47281093382566382680686050047210345/20476837392276624656401340676)*L (3728148112/3694509987)+
  (-12001466293/401953125)*H (327/200)+
  (-50995965659/1715000000)*H (527/327)+
  (-8)*H (1200/727)+
  (18196664416486466956587538550816/2203190304725340227508009122625)*(L (1327/824))^2

theorem lower_collection (f : ℝ → ℝ) :
    lowerPacket f = lowerPacket (fun _ => 0)+lowerCollected f f := by
  unfold lowerCollected
  lower_num
  ring

theorem lower_collected_payment : lowerCollected lowerLog V ≤ lowerCollected log log := by
  have h0 := log_le_V (by norm_num : (1:ℝ) ≤ 4/3)
  have h1 := log_lower (by norm_num : (1:ℝ) ≤ 3/2)
  have h2 := log_lower (by norm_num : (1:ℝ) ≤ 5/4)
  have h3 := log_le_V (by norm_num : (1:ℝ) ≤ 727/527)
  have h4 := log_lower (by norm_num : (1:ℝ) ≤ 1327/824)
  have h5 := log_lower (by norm_num : (1:ℝ) ≤ 116081/103506)
  have h6 := log_lower (by norm_num : (1:ℝ) ≤ 6466668/6152293)
  have h7 := log_le_V (by norm_num : (1:ℝ) ≤ 4315543337/4281905212)
  have h8 := log_lower (by norm_num : (1:ℝ) ≤ 3728148112/3694509987)
  have h9 := log_le_V (by norm_num : (1:ℝ) ≤ 327/200)
  have h10 := log_le_V (by norm_num : (1:ℝ) ≤ 527/327)
  have h11 := log_le_V (by norm_num : (1:ℝ) ≤ 1200/727)
  have hn : 0 ≤ lowerLog (1327/824:ℝ) := by norm_num [lowerLog]
  have hs := pow_le_pow_left₀ hn h4 2
  unfold lowerCollected
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,hs]

/-- Bilateral endpoint for the actual Q, with the same whole-log payment discipline. -/
def lowerRational : ℝ := rationalTotal+
  (lowerPacket (fun _ => 0)+lowerCollected lowerLog V-logPayment-JointJLossStrength.fixedRecovery)/4+
  3/10000

theorem actual_lower : lowerRational < JointHMotherPayment.unroundedCoefficient := by
  have hr := fixedCertificate_exact
  unfold fixedCertificate classicalPayment at hr
  have hp := PsiG18Strength.two_recoveries_bounds.1
  have hc := lower_collected_payment
  have hl := lower_real_actual
  unfold lowerReal at hl
  rw [lower_collection] at hl
  unfold lowerRational retainedExtra Phase20.psiPaymentLoss at *
  linarith only [hr,hp,hc,hl]

theorem actual_Q_enclosure : lowerRational < JointHMotherPayment.unroundedCoefficient ∧
    JointHMotherPayment.unroundedCoefficient < upperRational := ⟨actual_lower,actual_upper⟩

def lowerRemainder : ℝ := 8*V (5000/4469)-lowerRational

theorem actual_target_enclosure : -upperRemainder <
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient < lowerRemainder := by
  have htL := log_lower (by norm_num : (1:ℝ) ≤ 5000/4469)
  have htH := log_le_V (by norm_num : (1:ℝ) ≤ 5000/4469)
  unfold upperRemainder lowerRemainder AnalyticTotalThreshold.target
  constructor <;> linarith only [actual_lower,actual_upper,htL,htH]

macro "all_num" : tactic => `(tactic| norm_num [lowerRational,lowerRemainder,lowerPacket,lowerCollected,ExactWeightTripleEnclosure.lowerEnvelope,FifthLogTotalMagnitude.f0,FifthLogTotalMagnitude.slope,FifthLogTotalMagnitude.lo,FourActualCapRecovery.recovery_exact,FourTrueLowerTight.actual_lower_exact,FifthActualIntegralRecovery.recurrenceCap_exact.1,SixthFullRationalEnclosure.payment_rational,upperRational,upperRemainder,rationalTotal,collected,logPayment,UnroundedPayments.weightedJUpper,UnroundedPayments.j7Upper,UnroundedPayments.j8Upper,UnroundedPayments.j9Upper,JointJLossStrength.fixedRecovery,JointJLossStrength.massPayment,Phase24.newFour,Phase24.exactMass,Phase24.A,Phase24.c,FourLogAffine.w,FourLogAffine.l,FourLogAffine.u,FourRoughClosedMass.alpha,FourRoughClosedMass.beta,FourRoughClosedMass.lam,truncatedSixthLowerLambda,Phase20.fixedPsi,packet,mainLogs,base,jLower,JCorrelatedResidualTight.C,JCorrelatedResidualTight.R,JCubicPrimitive.rationalPart,JCubicPrimitive.crossRatio,ExactWeightTripleEnclosure.upperEnvelope,FifthLogTotalMagnitude.cap,FifthLogTotalMagnitude.hi,SharpJBalance.a,SharpJBalance.b,ninthProfileK2,c2,c43,c54,cH,cD,rH,A1,H,gap,quad,lin,
  FifthClassicalShape.ell,FifthClassicalShape.k,FifthClassicalShape.c,FifthClassicalShape.f,
  FifthClassicalShape.q,SharpMassBalance.s0,SharpMassBalance.fifthDensity,
  SharpMassBalance.a,SharpMassBalance.b,lowerLog,upperLog,V,
  SignedTotalCorrelation.jTwo,SharpJBalance.ninthA,SharpJBalance.s,
  SeventhEighth.sigma,SeventhEighth.alpha,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,
  Phase25.ratioz,Phase25.ratiob,Phase25.ratiom,Phase25.ratiop,
  Phase25.polez,Phase25.poleb,Phase25.polem,Phase25.polep,
  Phase25.kx,Phase25.qb1,Phase25.qm1,Phase25.qp1,
  a,b,s,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerSigma])

/-- Neither direction follows from these fully correlated endpoint payments. -/
theorem rational_endpoints_straddle :
    lowerRational < 8*lowerLog (5000/4469) ∧ 8*V (5000/4469) < upperRational := by
  all_num

/-- Exact rational residual, not a proportion of an older cap. -/
theorem upperRemainder_exact : upperRemainder =
    97379429185426419897091091437079519108732636894918445627135447682584352642886586542276371593605832439707771042569230482828179045263912806368420560944435745133510244752470759803836211792410106540917626548021098961800317642688364383647096517906560477548228308610263587466746081700691012960334963664791146569829224924747947256960877920359146979/5141840155799971092304928492869549877266665216017906556791138441201507408370388193667714174803904937166864357687699658937674579402850535256146363418274102287857847200223487682546723762725565341337760098314484060895368382351551175319988555085254870749902788875427667383560294053457618069220781750929257529100285571924017246845809728768000000000 := by all_num

theorem lowerRemainder_exact : lowerRemainder =
    36928296777450484713898402362965851880377980556015736144825576528580739744313888722641332290368644684659093377184917047898503764543780415807888684214441688353629563496771420983178778951890982168875935267302824984140362563175110059057270448928064742010750167059064154905796887203852662997432446760576337559265184481181/484972831888388517835352756518822935863352993637431038563049788751342165786519888738930554548738982631700430977556172174522124524894603188223199574643781440365205276276651890169259658394994877592357442842350743615154132257000630397805102565330740122761206661387716578516706351396018780781495611923751051809950000000000 := by all_num

theorem actual_Q_rational_bounds : (822040/1000000:ℝ) < JointHMotherPayment.unroundedCoefficient ∧
    JointHMotherPayment.unroundedCoefficient < 917123/1000000 := by
  have hl : (822040/1000000:ℝ) < lowerRational := by all_num
  have hu : upperRational < (917123/1000000:ℝ) := by all_num
  exact ⟨hl.trans actual_lower,actual_upper.trans hu⟩

theorem actual_target_rational_bounds : (-18939/1000000:ℝ) <
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient < 76146/1000000 := by
  have hl : (-18939/1000000:ℝ) < -upperRemainder := by all_num
  have hu : lowerRemainder < (76146/1000000:ℝ) := by all_num
  exact ⟨hl.trans actual_target_enclosure.1,actual_target_enclosure.2.trans hu⟩

theorem upper_remainder_size : (18938/1000000:ℝ) < upperRemainder ∧
    upperRemainder < 18939/1000000 := by all_num

end
end Wu2008DoubleSieve.GlobalSignedActualComparison
