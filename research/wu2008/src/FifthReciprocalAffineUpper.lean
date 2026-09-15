import FourMovingLogChord

namespace Wu2008DoubleSieve.FifthReciprocalAffineUpper
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpMassBalance SharpLogRecurrence
open FifthLogTotalMagnitude
open scoped Interval
noncomputable section

/-- Only the original tangent coefficient, not the Four geometric beta. -/
def coefficient : ℝ := hi FifthClassicalShape.q-FifthClassicalShape.q/(FifthClassicalShape.q-1)
def rate : ℝ := coefficient/(s0*FifthClassicalShape.q*a^2)

macro "fifth_num" : tactic => `(tactic| norm_num [coefficient,rate,hi,cap,
  JointLogTotalComparison.V,lowerLog,upperLog,FifthClassicalShape.q,s0,a,b,
  truncatedSixthLowerAlpha,truncatedSixthLowerBeta])

theorem coefficient_nonneg : 0 ≤ coefficient := by fifth_num

theorem reciprocal_chord {z : ℝ} (hz : s0 ≤ z) (hq : z ≤ FifthClassicalShape.q) :
    1/z ≤ (s0+FifthClassicalShape.q-z)/(s0*FifthClassicalShape.q) := by
  have hp := FifthClassicalShape.parameters
  have hs : 0 < s0 := by linarith [hp.1]
  have hz0 := hs.trans_le hz
  have hq0 := hs.trans hp.2.1
  apply (div_le_div_iff₀ hz0 (mul_pos hs hq0)).2
  nlinarith only [mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hq)]

theorem scalar_upper {z : ℝ} (hz : s0 ≤ z) (hq : z ≤ FifthClassicalShape.q) :
    log (z-1)/z ≤ cap-coefficient*(z-s0)/(s0*FifthClassicalShape.q) := by
  have hp := FifthClassicalShape.parameters
  have hs : 0 < s0 := by linarith [hp.1]
  have hz0 := hs.trans_le hz
  have hQ := (endpoint_logs (show 3 ≤ FifthClassicalShape.q by linarith [hp.1,hp.2.1])).2
  have ht := log_tangent (show 0 < z-1 by linarith [hp.1,hz])
    (show 0 < FifthClassicalShape.q-1 by linarith [hp.1,hp.2.1])
  rw [show z-1-(FifthClassicalShape.q-1)=z-FifthClassicalShape.q by ring] at ht
  have hdiv := div_le_div_of_nonneg_right (show log (z-1) ≤ hi FifthClassicalShape.q+
    (z-FifthClassicalShape.q)/(FifthClassicalShape.q-1) by linarith only [ht,hQ]) hz0.le
  have he : (hi FifthClassicalShape.q+(z-FifthClassicalShape.q)/(FifthClassicalShape.q-1))/z =
    1/(FifthClassicalShape.q-1)+coefficient/z := by unfold coefficient; field_simp; ring
  rw [he] at hdiv
  have hr := mul_le_mul_of_nonneg_left (reciprocal_chord hz hq) coefficient_nonneg
  have hid : 1/(FifthClassicalShape.q-1)+coefficient*((s0+FifthClassicalShape.q-z)/(s0*FifthClassicalShape.q)) =
      cap-coefficient*(z-s0)/(s0*FifthClassicalShape.q) := by
    unfold cap coefficient
    field_simp [hs.ne', (hs.trans hp.2.1).ne']; ring
  simp only [div_eq_mul_inv,one_mul] at hdiv hr hid ⊢
  linarith only [hdiv,hr,hid]

/-- The negative affine slope retains the shared x+y and the original reciprocal weight. -/
theorem kernel_upper {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    FifthActualIntegralRecovery.logRegular x y ≤ kernel (cap/a) (-rate) x y := by
  have ha := truncatedSixthLower_parameters.1
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hp := FifthActualIntegralRecovery.parameter_range hx hxy hy
  have hh := scalar_upper hp.1 hp.2
  have h := div_le_div_of_nonneg_right hh (mul_pos ha (mul_pos hx0 hy0)).le
  have hz : 0 < 1/2-x-y := by
    have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
    linarith [hxy.trans hy]
  rw [FifthActualIntegralRecovery.log_literal hx hxy hy]
  convert h using 1 <;> first | rfl |
    (dsimp [kernel,rate,s0,truncatedSixthLowerS,truncatedSixthLowerC];
     field_simp [ha.ne',hx0.ne',hy0.ne',hz.ne']; ring)

/-- Complete original triangle, using the unchanged double FTC for arbitrary real slope. -/
theorem integral_upper : FifthActualIntegralRecovery.logIntegral ≤ endpoint (cap/a) (-rate) :=
  endpoint_upper_comparison _ _ (fun _ _ hx hxy hy => kernel_upper hx hxy hy)

def descent (D : ℝ) : ℝ := 4*rate*(b*D^2-(b-a)*D)

theorem endpoint_descent : endpoint (cap/a) 0-endpoint (cap/a) (-rate) =
    descent (log b-log a) := by unfold endpoint descent; ring

theorem descent_mono {u v : ℝ} (hu : dLower ≤ u) (hv : u ≤ v) :
    descent u ≤ descent v := by
  have hb : 0 ≤ b := by fifth_num
  have hr : 0 ≤ rate := by fifth_num
  have hbase : 0 ≤ 2*b*dLower-(b-a) := by
    norm_num [dLower,lowerLog,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hm := mul_le_mul_of_nonneg_left (show 2*dLower ≤ v+u by linarith only [hu,hv]) hb
  have hn : 0 ≤ b*(v+u)-(b-a) := by linarith only [hbase,hm]
  have h := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hr)
    (mul_nonneg (sub_nonneg.mpr hv) hn)
  have he : descent v-descent u = 4*rate*((v-u)*(b*(v+u)-(b-a))) := by unfold descent; ring
  linarith only [h,he]

/-- Exact-endpoint descent is measured against the entire original integral cap. -/
theorem true_endpoint_gain_bounds : (3881/1000000:ℝ) <
    endpoint (cap/a) 0-endpoint (cap/a) (-rate) ∧
    endpoint (cap/a) 0-endpoint (cap/a) (-rate) < 3897/1000000 := by
  rw [endpoint_descent]
  have hl := descent_mono (le_refl dLower) log_ratio_bounds.1
  have hu := descent_mono log_ratio_bounds.1 log_ratio_bounds.2
  have hh : (3881/1000000:ℝ) < descent dLower ∧ descent dUpper < 3897/1000000 := by
    unfold descent dLower dUpper
    fifth_num
  exact ⟨hh.1.trans_le hl,hu.trans_lt hh.2⟩

theorem true_integral_upper_gain : (3881/1000000:ℝ) <
    endpoint (cap/a) 0-FifthActualIntegralRecovery.logIntegral := by
  have h := true_endpoint_gain_bounds.1
  have hi := integral_upper
  linarith only [h,hi]

open JointLogTotalComparison TotalEndpointComparison
open GlobalSignedActualComparison
open SixthExactEnvelopeGap (payment sixth_log_loss_enclosure)

def upperReal : ℝ :=
  (rationalPart+packet log+FifthActualIntegralRecovery.recurrenceCap+
    payment+1/100000+
    Phase24.newFour-FourMovingLogChord.actualLower-descent (log (b/a)))/4+retainedExtra

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
  have h5 := integral_upper
  have e5 := FifthActualIntegralRecovery.integral_distance.2
  have h6 := sixth_log_loss_enclosure.2
  have e6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.2
  have h4 := FourMovingLogChord.actual_four_lower
  rw [cancelled_actual_identity]
  unfold upperReal packet mainLogs logTotal D AnalyticTotalThreshold.fourLoss
    AnalyticTotalThreshold.fifthEndpoint FifthLogTotalMagnitude.endpoint descent at *
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])] at h5
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])]
  rw [log_two]
  unfold SignedTotalCorrelation.d2 SignedTotalCorrelation.e2 at hj
  rw [log_two] at hj
  linarith only [ht,hj,h5,e5,h6,e6,h4]


/-- The signed packet is recollected at the same log argument, before any payment. -/
def repaid (L H : ℝ → ℝ) : ℝ :=
  (-266739877032261626921/1785355070677447500)*L (4/3)+
  (358245804565677612772391597/14901576789423697560495000)*H (3/2)+
  (943083088/114604875)*H (5/4)+
  (15549918691125832337/2550817852506000000)*H (727/527)+
  (461394545660482807693814858876488341099518447932237377615313/34890579029137034319347960782331354090226470148728305943475)*H (1327/824)+
  (12963658609426086898463268417154149083835937/982672734630224359211166378158240922977124)*H (116081/103506)+
  (45711723750549248/1247524545012993)*H (6466668/6152293)+
  (-23526084706383522589366104523783786496/3729428911866529810567814389353)*L (4315543337/4281905212)+
  (47281093382566382680686050047210345/20476837392276624656401340676)*H (3728148112/3694509987)+
  (16/1)*H (26/25)+
  (20466702299/7640325000)*H (327/200)+
  (0/1)*H (527/327)+
  (37143670687/1528065000)*H (1200/727)+
  (907616/3472875)*H (1127/1000)+
  (-128/3)*L (2654/2181)+
  (-128/3)*L (5781/5308)+
  (-448/81)*L (1227/800)+
  (-18056918400/2336752783)*L (74881/66350)+
  (-18056918400/2336752783)*L (240187/198481)+
  (5627751922074057402143/766925223902696565000)*(H (1327/824))^2


theorem repaid_identity (f : ℝ → ℝ) : repaid f f =
    GlobalLogRelationPayment.repaid f f-descent (f (b/a)) := by
  unfold repaid GlobalLogRelationPayment.repaid descent
  fifth_num
  ring

theorem repaid_log_identity : repaid log log = collected log log-descent (log (b/a)) := by
  rw [repaid_identity,GlobalLogRelationPayment.repaid_log_identity]

theorem repaid_payment : collected log log-descent (log (b/a)) ≤ repaid lowerLog V := by
  rw [← repaid_log_identity]
  have h0 := log_lower (by norm_num : (1:ℝ) ≤ 4/3)
  have h1 := log_le_V (by norm_num : (1:ℝ) ≤ 3/2)
  have h2 := log_le_V (by norm_num : (1:ℝ) ≤ 5/4)
  have h3 := log_le_V (by norm_num : (1:ℝ) ≤ 727/527)
  have h4 := log_le_V (by norm_num : (1:ℝ) ≤ 1327/824)
  have h5 := log_le_V (by norm_num : (1:ℝ) ≤ 116081/103506)
  have h6 := log_le_V (by norm_num : (1:ℝ) ≤ 6466668/6152293)
  have h7 := log_lower (by norm_num : (1:ℝ) ≤ 4315543337/4281905212)
  have h8 := log_le_V (by norm_num : (1:ℝ) ≤ 3728148112/3694509987)
  have h9 := log_le_V (by norm_num : (1:ℝ) ≤ 26/25)
  have h10 := log_le_V (by norm_num : (1:ℝ) ≤ 327/200)
  have h11 := log_le_V (by norm_num : (1:ℝ) ≤ 527/327)
  have h12 := log_le_V (by norm_num : (1:ℝ) ≤ 1200/727)
  have h13 := log_le_V (by norm_num : (1:ℝ) ≤ 1127/1000)
  have h14 := log_lower (by norm_num : (1:ℝ) ≤ 2654/2181)
  have h15 := log_lower (by norm_num : (1:ℝ) ≤ 5781/5308)
  have h16 := log_lower (by norm_num : (1:ℝ) ≤ 1227/800)
  have h17 := log_lower (by norm_num : (1:ℝ) ≤ 74881/66350)
  have h18 := log_lower (by norm_num : (1:ℝ) ≤ 240187/198481)
  have hn : 0 ≤ log (1327/824:ℝ) := log_nonneg (by norm_num)
  have hs := pow_le_pow_left₀ hn h4 2
  unfold repaid
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,hs]

def motherGain : ℝ := descent (V (b/a))/4

theorem paid_descent : repaid lowerLog V = GlobalLogRelationPayment.repaid lowerLog V-4*motherGain := by
  unfold repaid GlobalLogRelationPayment.repaid motherGain descent
  fifth_num

/-- Only a certificate identity; the actual bound is reassembled from its producers below. -/
def upperRational : ℝ := FourMovingLogChord.upperRational-motherGain

theorem actual_upper : JointHMotherPayment.unroundedCoefficient < upperRational := by
  have hr := fixedCertificate_exact
  unfold fixedCertificate classicalPayment at hr
  have hp := PsiG18Strength.psi_loss_upper
  have hg := PsiG18Strength.g18_bounds.2
  have hc := repaid_payment
  have hu := actual_upper_real
  unfold upperReal at hu
  rw [collection] at hu
  rw [paid_descent] at hc
  unfold upperRational FourMovingLogChord.upperRational SixthExactEnvelopeGap.upperRational FourMovingLogChord.motherGain GlobalLogRelationPayment.upperRational
    BuchstabSeedTightLower.upperRational GlobalLogRelationPayment.logGain
    retainedExtra Phase20.psiPaymentLoss at *
  linarith only [hr,hp,hg,hc,hu]

def upperRemainder : ℝ := upperRational-8*lowerLog (5000/4469)

theorem remainder_substitution : upperRemainder = FourMovingLogChord.upperRemainder-motherGain := by
  unfold upperRemainder upperRational FourMovingLogChord.upperRemainder
  ring

theorem rate_exact : rate = 1286793306901659731/7445875960220355000 := by
  fifth_num

theorem mother_gain_exact : motherGain = 4799730124414782350970574993758260483764550177093/4927802877542168072074824454091728232184714831360000 := by
  norm_num [motherGain,descent,rate_exact,b,a,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,V,upperLog,lowerLog]

theorem upper_exact : upperRational = 7450601916137184166176725450133372653126791646033957271797344843740696429918794521953146836935325524225281419247535188187744783907146693213648742634382009429261788815971212262141454187507202324612014593047152974579831321365096479325976692470388472987895088709464904229735109117198545949529863259844894554635322275939913276908767029744975468908114411305154066900168412884812932990579938960043492199817003389751558355284417442609281327166604774176710049555840311379/8295923614173470097431756222379657741048568890212362544185373349581188361671761284571955555785173841347688794434030227190867621339492450326542914669253924909990415200573372987743137277201081878940646244943156054171908339274487057166014892896465742761875553899816272380216187077133830954211821576885703755891136439279200773116806806768422210348084360694363171663559449140493800057984758444191646176021979225672444640693132924471891249412629881421824000000000000000 := by
  rw [upperRational,FourMovingLogChord.upper_exact,mother_gain_exact]
  norm_num

theorem remainder_exact : upperRemainder = -114965672576874740600326826961650426483516596689004754361980382586864196573704324851870361051727251781951231929123483423362868229440216294901366109596916578563844396795210011968771381101806430861352670508296934900085038521533337207374437976367027006629668219398714540957345498250705747593530708049118635841625691609779106209993478809763275563176565585348345271023862142451019621561329980284171820246128580787564367246286166087205347224982028305621114274005273881982353/1433607716993153642811764449484046004017935639438058863702829118258157258167308362594880704049324480301083459136890438283346895179696599624297304292404298048815586293338417436613396572592697657685717302163984657016484677425824676594275317659973229325953924698078302970157158346242987513280287731850817476440738338356512547686904920611154595842423533425333472162514344133768706962623670320661471817196806169261607204473034914753255242049133587501250387116032000000000000000 := by
  rw [remainder_substitution,FourMovingLogChord.remainder_exact,mother_gain_exact]
  norm_num

theorem gain_bounds : (974/1000000:ℝ) < motherGain ∧ motherGain < 975/1000000 := by
  rw [mother_gain_exact]
  norm_num

theorem upper_bounds : (898103/1000000:ℝ) < upperRational ∧ upperRational < 898104/1000000 := by
  rw [upper_exact]
  norm_num

theorem remainder_bounds : (-81/1000000:ℝ) < upperRemainder ∧ upperRemainder < -80/1000000 := by
  rw [remainder_exact]
  norm_num

theorem actual_Q_bounds : (823047/1000000:ℝ) < JointHMotherPayment.unroundedCoefficient ∧
    JointHMotherPayment.unroundedCoefficient < 898104/1000000 :=
  ⟨FourMovingLogChord.actual_Q_bounds.1,actual_upper.trans upper_bounds.2⟩

/-- The real target direction now closes, not just a conditional or tiny positive gain. -/
theorem target_gap_positive : (80/1000000:ℝ) <
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient := by
  have ht := log_lower (by norm_num : (1:ℝ) ≤ 5000/4469)
  have hu := actual_upper
  have hr := remainder_bounds.2
  unfold upperRemainder AnalyticTotalThreshold.target at *
  linarith only [ht,hu,hr]

theorem actual_below_target : JointHMotherPayment.unroundedCoefficient < AnalyticTotalThreshold.target := by
  have h := target_gap_positive
  linarith only [h]

end
end Wu2008DoubleSieve.FifthReciprocalAffineUpper
