import JJointEnvelope
open Real Wu2008DoubleSieve
open SharpLogRecurrence JointLogTotalComparison GlobalSignedActualComparison
open FixedCoefficientUpperEnclosure (a b)
open OldPackageWidth
noncomputable section
namespace WidthIntervals

def sharedPaid (L H : ℝ → ℝ) : ℝ :=
  (-3352989216407714659843038187/804589349441235833475000000)+
  (8/1)*L (3/2)+
  (4/1)*L (26/25)+
  (828418637/14470312500)*L (327/200)+
  (-3930785284831/6112260000000)*H (527/327)+
  (384240583/216000000)*L (727/527)+
  (226904/3472875)*L (1127/1000)+
  (8879658527/5730243750)*L (5/4)+
  (1/2)*L (4/3)

theorem shared_formula (f : ℝ → ℝ) : shared f = sharedPaid f f := by
  unfold sharedPaid
  norm_num [shared,base,ExactWeightTripleEnclosure.upperEnvelope,
    ExactWeightTripleEnclosure.lowerEnvelope,BaseSharedSlack.gain,lowerLog]
  ring

theorem shared_payment : sharedPaid lowerLog V ≤ shared log ∧
    shared log ≤ sharedPaid V lowerLog := by
  rw [shared_formula]
  have l0 := log_lower (by norm_num : (1:ℝ) ≤ (26/25))
  have h0 := log_le_V (by norm_num : (1:ℝ) ≤ (26/25))
  have l1 := log_lower (by norm_num : (1:ℝ) ≤ (1127/1000))
  have h1 := log_le_V (by norm_num : (1:ℝ) ≤ (1127/1000))
  have l2 := log_lower (by norm_num : (1:ℝ) ≤ (5/4))
  have h2 := log_le_V (by norm_num : (1:ℝ) ≤ (5/4))
  have l3 := log_lower (by norm_num : (1:ℝ) ≤ (4/3))
  have h3 := log_le_V (by norm_num : (1:ℝ) ≤ (4/3))
  have l4 := log_lower (by norm_num : (1:ℝ) ≤ (727/527))
  have h4 := log_le_V (by norm_num : (1:ℝ) ≤ (727/527))
  have l5 := log_lower (by norm_num : (1:ℝ) ≤ (3/2))
  have h5 := log_le_V (by norm_num : (1:ℝ) ≤ (3/2))
  have l6 := log_lower (by norm_num : (1:ℝ) ≤ (527/327))
  have h6 := log_le_V (by norm_num : (1:ℝ) ≤ (527/327))
  have l7 := log_lower (by norm_num : (1:ℝ) ≤ (327/200))
  have h7 := log_le_V (by norm_num : (1:ℝ) ≤ (327/200))
  unfold sharedPaid
  constructor <;> nlinarith only [l0,h0,l1,h1,l2,h2,l3,h3,l4,h4,l5,h5,l6,h6,l7,h7]

theorem shared_bounds : (23087/1000000:ℝ) < shared log ∧
    shared log < 24464/1000000 := by
  have hl : (23087/1000000:ℝ) < sharedPaid lowerLog V := by
    norm_num [sharedPaid,lowerLog,upperLog,V]
  have hu : sharedPaid V lowerLog < (24464/1000000:ℝ) := by
    norm_num [sharedPaid,lowerLog,upperLog,V]
  exact ⟨hl.trans_le shared_payment.1,shared_payment.2.trans_lt hu⟩

def jPaid (L H : ℝ → ℝ) : ℝ :=
  (179579971243232777247933012889723905048710064906043141994045803257386930964287989150417920794476637280712007/43017824535733324069161959611446598064430140623688666430097655351517060915657750515605921807214144732088000)+
  (11671704739535407/265163603902367967)*L (4/3)+
  (11671704739535407/265163603902367967)*L (3/2)+
  (-32/3)*H (2654/2181)+
  (-32/3)*H (5781/5308)+
  (-112/81)*H (1227/800)+
  (-4514229600/2336752783)*H (74881/66350)+
  (-4514229600/2336752783)*H (240187/198481)

theorem j_formula (f : ℝ → ℝ) : j f = jPaid f f := by
  unfold jPaid
  norm_num [j,jLower,JCorrelatedResidualTight.C,JCorrelatedResidualTight.R,
    JCubicPrimitive.rationalPart,JCubicPrimitive.crossRatio,SharpJBalance.a,SharpJBalance.s,
    SharpJBalance.b,ninthProfileK2,SeventhEighth.sigma,SeventhEighth.alpha,
    UnroundedPayments.weightedJUpper,UnroundedPayments.j7Upper,UnroundedPayments.j8Upper,
    UnroundedPayments.j9Upper,SignedTotalCorrelation.jTwo,SharpJBalance.ninthA,
    JointJLossStrength.fixedRecovery,JointJLossStrength.massPayment,upperLog,lowerLog]
  ring

theorem j_payment : jPaid lowerLog V ≤ j log ∧
    j log ≤ jPaid V lowerLog := by
  rw [j_formula]
  have l0 := log_lower (by norm_num : (1:ℝ) ≤ (5781/5308))
  have h0 := log_le_V (by norm_num : (1:ℝ) ≤ (5781/5308))
  have l1 := log_lower (by norm_num : (1:ℝ) ≤ (74881/66350))
  have h1 := log_le_V (by norm_num : (1:ℝ) ≤ (74881/66350))
  have l2 := log_lower (by norm_num : (1:ℝ) ≤ (240187/198481))
  have h2 := log_le_V (by norm_num : (1:ℝ) ≤ (240187/198481))
  have l3 := log_lower (by norm_num : (1:ℝ) ≤ (2654/2181))
  have h3 := log_le_V (by norm_num : (1:ℝ) ≤ (2654/2181))
  have l4 := log_lower (by norm_num : (1:ℝ) ≤ (4/3))
  have h4 := log_le_V (by norm_num : (1:ℝ) ≤ (4/3))
  have l5 := log_lower (by norm_num : (1:ℝ) ≤ (3/2))
  have h5 := log_le_V (by norm_num : (1:ℝ) ≤ (3/2))
  have l6 := log_lower (by norm_num : (1:ℝ) ≤ (1227/800))
  have h6 := log_le_V (by norm_num : (1:ℝ) ≤ (1227/800))
  unfold jPaid
  constructor <;> nlinarith only [l0,h0,l1,h1,l2,h2,l3,h3,l4,h4,l5,h5,l6,h6]

theorem j_bounds : (7297/1000000:ℝ) < j log ∧
    j log < 7591/1000000 := by
  have hl : (7297/1000000:ℝ) < jPaid lowerLog V := by
    norm_num [jPaid,lowerLog,upperLog,V]
  have hu : jPaid V lowerLog < (7591/1000000:ℝ) := by
    norm_num [jPaid,lowerLog,upperLog,V]
  exact ⟨hl.trans_le j_payment.1,j_payment.2.trans_lt hu⟩

def fifthPaid (L H : ℝ → ℝ) : ℝ :=
  (-65216423715278935221942009918380973061309825/18795369635993700794366782815755472336441848412)+
  (6527352962572434038483149180794409/46129517324217283547471691805873200)*L (1327/824)+
  (-531159961203897726688943111950479307/2306475866210864177373584590293660000)*H (1327/824)*H (1327/824)

theorem fifth_formula (f : ℝ → ℝ) : fifth f = fifthPaid f f := by
  unfold fifthPaid
  norm_num [fifth,FifthReciprocalAffineUpper.descent,FifthReciprocalAffineUpper.rate,
    FifthReciprocalAffineUpper.coefficient,FifthLogTotalMagnitude.cap,FifthLogTotalMagnitude.hi,
    FifthLogTotalMagnitude.f0,FifthLogTotalMagnitude.lo,FifthLogTotalMagnitude.slope,
    FifthClassicalShape.q,SharpMassBalance.s0,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,
    V,upperLog,lowerLog,GlobalLowerSlack.fifthGain_exact]
  ring

theorem fifth_payment : fifthPaid lowerLog V ≤ fifth log ∧
    fifth log ≤ fifthPaid V lowerLog := by
  rw [fifth_formula]
  have l0 := log_lower (by norm_num : (1:ℝ) ≤ (1327/824))
  have h0 := log_le_V (by norm_num : (1:ℝ) ≤ (1327/824))
  have ls0 := pow_le_pow_left₀ (show 0 ≤ lowerLog (1327/824) by norm_num [lowerLog]) l0 2
  have hs0 := pow_le_pow_left₀ (log_nonneg (by norm_num : (1:ℝ) ≤ (1327/824))) h0 2
  unfold fifthPaid
  constructor <;> nlinarith only [l0,h0,ls0,hs0]

theorem fifth_bounds : (11624/1000000:ℝ) < fifth log ∧
    fifth log < 11732/1000000 := by
  have hl : (11624/1000000:ℝ) < fifthPaid lowerLog V := by
    norm_num [fifthPaid,lowerLog,upperLog,V]
  have hu : fifthPaid V lowerLog < (11732/1000000:ℝ) := by
    norm_num [fifthPaid,lowerLog,upperLog,V]
  exact ⟨hl.trans_le fifth_payment.1,fifth_payment.2.trans_lt hu⟩

end WidthIntervals
