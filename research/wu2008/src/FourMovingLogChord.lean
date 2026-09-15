import SixthExactEnvelopeGap

namespace Wu2008DoubleSieve.FourMovingLogChord
open Real Set MeasureTheory FourRoughClosedMass ClassicalLogFourBounds
open FourLogAffine (ell)
open BuchstabSeedTightLower (lower lower_pos regular_lower)
open JFourRemainingMagnitude.FourLower (ell_derivative compare_primitive)
open scoped Interval
noncomputable section
local notation "lower" => BuchstabSeedTightLower.lower

/-- The two real original endpoint logs remain unpaid through the full FTC. -/
def p : ℝ := log (lam-alpha)-log beta
def q : ℝ := log (lam-beta)-log beta
def c : ℝ := 1/((p-q)/(beta-alpha))
def A : ℝ := p+alpha/c

theorem width_pos : 0 < beta-alpha := by
  norm_num [alpha,beta,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

/-- Jensen's log inequality on the complete original endpoint interval. -/
theorem moving_log_lower {z : ℝ} (hz : alpha ≤ z) (hzb : z ≤ beta) :
    log (lam-alpha)-(z-alpha)/c ≤ log (lam-z) := by
  have ha : 0 < lam-alpha := Phase24.c_pos
  have hb : 0 < lam-beta := JFourRemainingMagnitude.FourLower.c_pos
  have ht : 0 < lam-z := hb.trans_le (by linarith)
  have h1 := log_le_sub_one_of_pos (div_pos ha ht)
  have h2 := log_le_sub_one_of_pos (div_pos hb ht)
  rw [log_div ha.ne' ht.ne'] at h1
  rw [log_div hb.ne' ht.ne'] at h2
  have h1' := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hzb)
  have h2' := mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hz)
  have he : (beta-z)*((lam-alpha)/(lam-z)-1)+
      (z-alpha)*((lam-beta)/(lam-z)-1) = 0 := by
    field_simp
    ring
  have h : (beta-z)*log (lam-alpha)+(z-alpha)*log (lam-beta) ≤
      (beta-alpha)*log (lam-z) := by nlinarith only [h1',h2',he]
  apply (mul_le_mul_iff_left₀ width_pos).mp
  have he' : (beta-alpha)*(log (lam-alpha)-(z-alpha)/c) =
      (beta-z)*log (lam-alpha)+(z-alpha)*log (lam-beta) := by
    simp only [c,p,q,div_eq_mul_inv,inv_inv,one_mul]
    field_simp [width_pos.ne']
    ring
  nlinarith only [he',h]

def Z (z : ℝ) : ℝ := -A*ell z-ell z^2/2-z/c
def F (y : ℝ) : ℝ :=
  (-ell y^2/2+(1-A)*ell y+(A-1+beta/c))/y+log y/c
def H (x : ℝ) : ℝ := F beta*log x-
  (ell x^2/2+(A-2)*ell x+(3-2*A-beta/c))/x-log x^2/(2*c)

theorem Z_derivative {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt Z ((A+ell z)/z-1/c) z := by
  convert (((ell_derivative hz).const_mul (-A)).sub
    (((ell_derivative hz).pow 2).div_const 2)).sub
    ((hasDerivAt_id z).div_const c) using 1 <;>
    first | rfl | (field_simp; ring)

theorem F_derivative {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt F ((A*ell y+ell y^2/2-(beta-y)/c)/y^2) y := by
  have he := ell_derivative hy
  convert (((((he.pow 2).neg.div_const 2).add (he.const_mul (1-A))).add_const
    (A-1+beta/c)).div (hasDerivAt_id y) hy).add
    ((hasDerivAt_log hy).div_const c) using 1 <;>
    first | rfl | (dsimp; field_simp; ring)

theorem H_derivative {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt H ((F beta-F x)/x) x := by
  have he := ell_derivative hx
  convert (((hasDerivAt_log hx).const_mul (F beta)).sub
    (((((he.pow 2).div_const 2).add (he.const_mul (A-2))).add_const
      (3-2*A-beta/c)).div (hasDerivAt_id x) hx)).sub
    (((hasDerivAt_log hx).pow 2).div_const (2*c)) using 1 <;>
    first | rfl | (dsimp [F]; field_simp; ring)

def exactMass (L : ℝ) : ℝ :=
  (1/(2*alpha)+1/(2*c))*L^2+
    ((A-2)/alpha+(A-1+beta/c)/beta)*L+
    (3-2*A-beta/c)*(1/alpha-1/beta)

theorem inner_lower {x y z : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) (hy : alpha ≤ y) (hyb : y ≤ beta)
    (hz : alpha ≤ z) (hzb : z ≤ beta) :
    lower/(x*y^2)*((A+ell z)/z-1/c) ≤
      regularInner10 x y z+regularInner11 x y z := by
  have hlower := lower_pos

  have hx0 := fixed_geometry.2.1.trans_le hx
  have hy0 := fixed_geometry.2.1.trans_le hy
  have hz0 := fixed_geometry.2.1.trans_le hz
  have hb0 := fixed_geometry.2.1.trans_le fixed_geometry.2.2.1
  have ho : z ≤ lam-z := by linarith [fixed_geometry.2.2.2.2.2.2.1]
  rw [Phase24.inner_join]
  have h := FourPositiveLogLower.log_tail_le_integral (C := lower/(x*y^2*z))
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    hz0 ho 0 (fun t ht => by
      have hh := regular_lower hx hxb hy hyb hz (hz.trans ht.1) ht.2
      convert hh using 1 <;> first | rfl | ring)
  norm_num only [Nat.cast_zero,zero_add,pow_one,div_one] at h
  have hl := moving_log_lower hz hzb
  have htail : A+ell z-z/c ≤ log (lam-z)-log z := by
    dsimp [A,p,ell]
    rw [sub_div] at hl
    linarith only [hl]
  have hm := mul_le_mul_of_nonneg_left htail
    (show 0 ≤ lower/(x*y^2*z) by positivity)
  refine le_trans ?_ (hm.trans h)
  apply le_of_eq
  field_simp

theorem middle_lower {x y : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) (hy : alpha ≤ y) (hyb : y ≤ beta) :
    lower/x*((A*ell y+ell y^2/2-(beta-y)/c)/y^2) ≤
      regularMiddle10 x y+regularMiddle11 x y := by
  have hlower := lower_pos

  have hi10 : Continuous (fun z => regularInner10 x y z) := regularInner10_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)
  have hi11 : Continuous (fun z => regularInner11 x y z) := regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)
  have hn : ∀ z ∈ Icc y beta, z ≠ 0 := fun z hz =>
    (fixed_geometry.2.1.trans_le (hy.trans hz.1)).ne'
  have he : ContinuousOn ell (Icc y beta) :=
    continuousOn_const.sub (continuousOn_id.log hn)
  have h := compare_primitive (f := fun z => regularInner10 x y z+regularInner11 x y z)
    (g := fun z => lower/(x*y^2)*((A+ell z)/z-1/c))
    (P := fun z => lower/(x*y^2)*Z z) hyb (hi10.add hi11)
    (continuousOn_const.mul (((continuousOn_const.add he).div continuousOn_id hn).sub continuousOn_const))
    (fun z hz => (Z_derivative (hn z hz)).const_mul _) (fun z hz =>
      inner_lower hx hxb hy hyb (hy.trans hz.1) hz.2)
  rw [intervalIntegral.integral_add (hi10.intervalIntegrable y beta) (hi11.intervalIntegrable y beta)] at h
  change _ ≤ regularMiddle10 x y+regularMiddle11 x y at h
  convert h using 1
  simp only [Z,ell,sub_self]
  ring

theorem outer_lower {x : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) :
    lower/x*(F beta-F x) ≤ regularOuter10 x+regularOuter11 x := by
  have hlower := lower_pos

  have hi10 : Continuous (fun y => regularMiddle10 x y) := regularMiddle10_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hi11 : Continuous (fun y => regularMiddle11 x y) := regularMiddle11_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hn : ∀ y ∈ Icc x beta, y ≠ 0 := fun y hy =>
    (fixed_geometry.2.1.trans_le (hx.trans hy.1)).ne'
  have he : ContinuousOn ell (Icc x beta) := continuousOn_const.sub (continuousOn_id.log hn)
  have hg : ContinuousOn (fun y => lower/x*((A*ell y+ell y^2/2-(beta-y)/c)/y^2)) (Icc x beta) :=
    continuousOn_const.mul ((((continuousOn_const.mul he).add ((he.pow 2).div_const 2)).sub
      ((continuousOn_const.sub continuousOn_id).div_const c)).div (continuousOn_id.pow 2)
        (fun y hy => pow_ne_zero 2 (hn y hy)))
  have h := compare_primitive (f := fun y => regularMiddle10 x y+regularMiddle11 x y) hxb (hi10.add hi11) hg
    (fun y hy => (F_derivative (hn y hy)).const_mul (lower/x))
    (fun y hy => middle_lower hx hxb (hx.trans hy.1) hy.2)
  rw [intervalIntegral.integral_add (hi10.intervalIntegrable x beta) (hi11.intervalIntegrable x beta)] at h
  change _ ≤ regularOuter10 x+regularOuter11 x at h
  convert h using 1; ring

theorem complete_real_lower : (8*lower)*exactMass tailLog ≤ 8*I10+8*I11 := by
  have hlower := lower_pos

  have hn : ∀ x ∈ Icc alpha beta, x ≠ 0 := fun x hx =>
    (fixed_geometry.2.1.trans_le hx.1).ne'
  have he : ContinuousOn ell (Icc alpha beta) := continuousOn_const.sub (continuousOn_id.log hn)
  have hf : ContinuousOn F (Icc alpha beta) := by
    exact (((((he.pow 2).neg.div_const 2).add (continuousOn_const.mul he)).add
      continuousOn_const).div continuousOn_id hn).add ((continuousOn_id.log hn).div_const c)
  have hg : ContinuousOn (fun x => lower*((F beta-F x)/x)) (Icc alpha beta) :=
    continuousOn_const.mul ((continuousOn_const.sub hf).div continuousOn_id hn)
  have h := compare_primitive (f := fun x => regularOuter10 x+regularOuter11 x) fixed_geometry.2.2.1
    (regularOuter10_continuous.add regularOuter11_continuous) hg
    (fun x hx => (H_derivative (hn x hx)).const_mul lower) (fun x hx => by
      convert outer_lower hx.1 hx.2 using 1; ring)
  rw [intervalIntegral.integral_add
    (regularOuter10_continuous.intervalIntegrable alpha beta)
    (regularOuter11_continuous.intervalIntegrable alpha beta),← I10_eq_regular,← I11_eq_regular] at h
  have heq : H beta-H alpha = exactMass tailLog := by
    dsimp [H,F,ell,exactMass,tailLog]
    ring
  have hh : lower*H beta-lower*H alpha = lower*exactMass tailLog := by rw [← heq]; ring
  rw [hh] at h
  linarith


open SharpLogRecurrence

/-- Endpoint coefficients of the already integrated whole mass. -/
def weightA (L : ℝ) : ℝ := (1/alpha+1/beta)*L-2*(1/alpha-1/beta)
def weightD (L : ℝ) : ℝ := alpha*weightA L+L^2/2+L-beta*(1/alpha-1/beta)
def weightP (L : ℝ) : ℝ := weightA L+weightD L/(beta-alpha)
def weightQ (L : ℝ) : ℝ := -weightD L/(beta-alpha)
def mass (P Q L : ℝ) : ℝ :=
  L^2/(2*alpha)+(-2/alpha-1/beta)*L+3*(1/alpha-1/beta)+
    P*weightP L+Q*weightQ L

theorem mass_identity (L : ℝ) : exactMass L = mass p q L := by
  unfold exactMass A c mass weightP weightQ weightD weightA
  simp only [div_eq_mul_inv,inv_inv,one_mul,mul_inv_rev]
  norm_num [alpha,beta,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  ring

def pLower : ℝ := lowerLog ((lam-alpha)/beta)
def qLower : ℝ := lowerLog ((lam-beta)/beta)

theorem endpoint_logs_lower : pLower ≤ p ∧ qLower ≤ q := by
  have ha : 0 < lam-alpha := Phase24.c_pos
  have hb : 0 < lam-beta := JFourRemainingMagnitude.FourLower.c_pos
  have hb0 := fixed_geometry.2.1.trans_le fixed_geometry.2.2.1
  constructor
  · have h := log_lower (t := (lam-alpha)/beta)
      (by norm_num [lam,alpha,beta,truncatedSixthLowerLambda,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
    rw [log_div ha.ne' hb0.ne'] at h
    exact h
  · have h := log_lower (t := (lam-beta)/beta)
      (by norm_num [lam,alpha,beta,truncatedSixthLowerLambda,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
    rw [log_div hb.ne' hb0.ne'] at h
    exact h

macro "fixed_num" : tactic => `(tactic| norm_num [alpha,beta,lam,
  truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda,
  FourLogAffine.l,FourLogAffine.u,pLower,qLower,lowerLog,upperLog])

theorem endpoint_weight_signs : 0 ≤ weightP tailLog ∧ 0 ≤ weightQ tailLog := by
  obtain ⟨hl0,hl,hu,_,_⟩ := FourLogAffine.fixed_log_bounds
  have hslo := pow_le_pow_left₀ hl0.le hl 2
  have hshi := pow_le_pow_left₀ (hl0.le.trans hl) hu 2
  have hpl : 0 ≤ weightP FourLogAffine.l := by
    unfold weightP weightD weightA
    fixed_num
  have hqu : 0 ≤ weightQ FourLogAffine.u := by
    unfold weightQ weightD weightA
    fixed_num
  constructor
  · unfold weightP weightD weightA at *
    norm_num [alpha,beta,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at *
    nlinarith only [hl,hslo,hpl]
  · unfold weightQ weightD weightA at *
    norm_num [alpha,beta,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at *
    nlinarith only [hu,hshi,hqu]

/-- Both endpoint logs are paid only after the full 8+8 weighted FTC. -/
theorem endpoint_payment : mass pLower qLower tailLog ≤ exactMass tailLog := by
  rw [mass_identity]
  have hp := mul_le_mul_of_nonneg_right endpoint_logs_lower.1 endpoint_weight_signs.1
  have hq := mul_le_mul_of_nonneg_right endpoint_logs_lower.2 endpoint_weight_signs.2
  unfold mass
  linarith only [hp,hq]

/-- Preserve the common tail logarithm rather than rounding signed terms separately. -/
theorem tail_payment : mass pLower qLower FourLogAffine.l ≤ mass pLower qLower tailLog := by
  have hl := FourLogAffine.fixed_log_bounds.2.1
  have hl0 := FourLogAffine.fixed_log_bounds.1
  have hp : 0 ≤ 1/(2*alpha)+(pLower-qLower)/(2*(beta-alpha)) := by fixed_num
  have hd : 0 ≤ 2*(1/(2*alpha)+(pLower-qLower)/(2*(beta-alpha)))*FourLogAffine.l+
      (-2/alpha-1/beta)+pLower*((1/alpha+1/beta)+(2+alpha/beta)/(beta-alpha))-
      qLower*(2+alpha/beta)/(beta-alpha) := by fixed_num
  have hm := mul_le_mul_of_nonneg_left
    (show 2*FourLogAffine.l ≤ tailLog+FourLogAffine.l by linarith only [hl]) hp
  have hn : 0 ≤ (1/(2*alpha)+(pLower-qLower)/(2*(beta-alpha)))*(tailLog+FourLogAffine.l)+
      (-2/alpha-1/beta)+pLower*((1/alpha+1/beta)+(2+alpha/beta)/(beta-alpha))-
      qLower*(2+alpha/beta)/(beta-alpha) := by linarith only [hm,hd]
  have h := mul_nonneg (sub_nonneg.mpr hl) hn
  have he : mass pLower qLower tailLog-mass pLower qLower FourLogAffine.l =
      (tailLog-FourLogAffine.l)*((1/(2*alpha)+(pLower-qLower)/(2*(beta-alpha)))*(tailLog+FourLogAffine.l)+
      (-2/alpha-1/beta)+pLower*((1/alpha+1/beta)+(2+alpha/beta)/(beta-alpha))-
      qLower*(2+alpha/beta)/(beta-alpha)) := by
    unfold mass weightP weightQ weightD weightA
    norm_num [alpha,beta,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
    ring
  linarith only [h,he]

def actualLower : ℝ := 8*lower*mass pLower qLower FourLogAffine.l

theorem actual_four_lower : actualLower ≤ 8*I10+8*I11 := by
  exact (mul_le_mul_of_nonneg_left (tail_payment.trans endpoint_payment)
    (mul_nonneg (by norm_num) lower_pos.le)).trans complete_real_lower

theorem actual_lower_exact : actualLower = 19648084138220666688542153209081893197432249009368489/28681628544472461681928961455272803239757101786005000 := by
  norm_num [actualLower,mass,weightP,weightQ,weightD,weightA,BuchstabSeedTightLower.lower, pLower,qLower,FourLogAffine.l,lowerLog,alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

def motherGain : ℝ := (actualLower-BuchstabSeedTightLower.actualLower)/4

theorem mother_gain_exact : motherGain = 505110037547023416757968421429815713557475569414339651/142963003847352095804341269794578182292504478710306202400 := by
  rw [motherGain,actual_lower_exact,BuchstabSeedTightLower.actual_lower_exact]
  norm_num

def remainingCap : ℝ := FourActualCapRecovery.actualUpper-actualLower

theorem four_remaining_interval : 0 ≤ JFourRemainingMagnitude.fourRemaining ∧
    JFourRemainingMagnitude.fourRemaining ≤ remainingCap := by
  have hl := actual_four_lower
  have hu := FourActualCapRecovery.actual_four_upper
  rw [JFourRemainingMagnitude.four_remaining_identity]
  unfold remainingCap
  constructor <;> linarith only [hl,hu]

theorem remaining_cap_exact : remainingCap = 44554008007514792172757180343586889380085086036202860046862021/1644970362092048571590074220308329126342600871906128544668192000 := by
  have he : remainingCap = BuchstabSeedTightLower.remainingCap-
      (actualLower-BuchstabSeedTightLower.actualLower) := by
    unfold remainingCap BuchstabSeedTightLower.remainingCap
    ring
  rw [he,BuchstabSeedTightLower.remaining_cap_exact,actual_lower_exact,
    BuchstabSeedTightLower.actual_lower_exact]
  norm_num

open JointLogTotalComparison TotalEndpointComparison ClassicalAnalyticLeaves
open FixedCoefficientUpperEnclosure (a b s)
open GlobalSignedActualComparison
open SixthExactEnvelopeGap (payment sixth_log_loss_enclosure)

def upperReal : ℝ :=
  (rationalPart+packet log+FifthActualIntegralRecovery.recurrenceCap+
    payment+1/100000+
    Phase24.newFour-actualLower)/4+retainedExtra

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
  have h6 := sixth_log_loss_enclosure.2
  have e6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.2
  have h4 := actual_four_lower
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


/-- Both new producer bounds enter the same original upper packet. -/
def upperRational : ℝ := SixthExactEnvelopeGap.upperRational-motherGain

theorem actual_upper : JointHMotherPayment.unroundedCoefficient < upperRational := by
  have hr := fixedCertificate_exact
  unfold fixedCertificate classicalPayment at hr
  have hp := PsiG18Strength.psi_loss_upper
  have hg := PsiG18Strength.g18_bounds.2
  have hc := GlobalLogRelationPayment.repaid_payment
  have hu := actual_upper_real
  unfold upperReal at hu
  rw [collection] at hu
  unfold upperRational SixthExactEnvelopeGap.upperRational motherGain GlobalLogRelationPayment.upperRational
    BuchstabSeedTightLower.upperRational GlobalLogRelationPayment.logGain
    retainedExtra Phase20.psiPaymentLoss at *
  linarith only [hr,hp,hg,hc,hu]

def upperRemainder : ℝ := upperRational-8*lowerLog (5000/4469)

theorem upper_substitution : upperRational = SixthExactEnvelopeGap.upperRational-motherGain := rfl

theorem remainder_substitution : upperRemainder = SixthExactEnvelopeGap.upperRemainder-motherGain := by
  unfold upperRemainder upperRational SixthExactEnvelopeGap.upperRemainder
  ring

theorem upper_exact : upperRational = 7458682230116921199443663558044163927605903685070097629779168660705765171240796899187080374740130335017492479179875822948547573827243316505663599668710548917446878051831687030071763910610836813000044663543092279146548683235934295794016591498254122790191926570814077903458939102773071709986097104475391325575017563404674671708134686120456462057145686090638322515503192980955078438149500384730773900278891360360309090275161985776964115745808843446489300755840311379/8295923614173470097431756222379657741048568890212362544185373349581188361671761284571955555785173841347688794434030227190867621339492450326542914669253924909990415200573372987743137277201081878940646244943156054171908339274487057166014892896465742761875553899816272380216187077133830954211821576885703755891136439279200773116806806768422210348084360694363171663559449140493800057984758444191646176021979225672444640693132924471891249412629881421824000000000000000 := by
  rw [upper_substitution,SixthExactEnvelopeGap.upper_exact,mother_gain_exact]
  norm_num

theorem remainder_exact : upperRemainder = 1281382825291110461956767712995150312056090669711390273029111183417891646436618627837139555862681221332336615123330040381334888616031688511543414574574124973590368540622164993546366953629173057197800656592836094603273566785984541608476784881066494923995280633267204645266157263091945011679323684912096290967498753434921085925728445910224396862872246218041239692890243714287477388834606403142912559390227932533064509293645435602137185742600162486395684116676326118017647/1433607716993153642811764449484046004017935639438058863702829118258157258167308362594880704049324480301083459136890438283346895179696599624297304292404298048815586293338417436613396572592697657685717302163984657016484677425824676594275317659973229325953924698078302970157158346242987513280287731850817476440738338356512547686904920611154595842423533425333472162514344133768706962623670320661471817196806169261607204473034914753255242049133587501250387116032000000000000000 := by
  rw [remainder_substitution,SixthExactEnvelopeGap.remainder_exact,mother_gain_exact]
  norm_num

/-- Strict exact descent of the parent upper certificate, backed by a new actual producer. -/
theorem upper_strict_descent : upperRational < SixthExactEnvelopeGap.upperRational ∧
    upperRemainder < SixthExactEnvelopeGap.upperRemainder := by
  have hg : 0 < motherGain := by rw [mother_gain_exact]; norm_num
  rw [upper_substitution,remainder_substitution]
  constructor <;> linarith only [hg]

theorem actual_lower_bounds : (685040/1000000:ℝ) < actualLower ∧ actualLower < 685041/1000000 := by
  rw [actual_lower_exact]
  norm_num

theorem gain_bounds : (3533/1000000:ℝ) < motherGain ∧ motherGain < 3534/1000000 := by
  rw [mother_gain_exact]
  norm_num

theorem upper_bounds : (899077/1000000:ℝ) < upperRational ∧ upperRational < 899078/1000000 := by
  rw [upper_exact]
  norm_num

theorem remainder_bounds : (893/1000000:ℝ) < upperRemainder ∧ upperRemainder < 894/1000000 := by
  rw [remainder_exact]
  norm_num

theorem remaining_cap_bounds : (27084/1000000:ℝ) < remainingCap ∧ remainingCap < 27085/1000000 := by
  rw [remaining_cap_exact]
  norm_num

theorem actual_four_magnitude : (685040/1000000:ℝ) < 8*I10+8*I11 :=
  actual_lower_bounds.1.trans_le actual_four_lower

theorem actual_Q_bounds : (823047/1000000:ℝ) < JointHMotherPayment.unroundedCoefficient ∧
    JointHMotherPayment.unroundedCoefficient < 899078/1000000 :=
  ⟨SixthExactEnvelopeGap.actual_Q_bounds.1,actual_upper.trans upper_bounds.2⟩

theorem actual_target_bounds : (-894/1000000:ℝ) <
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient < 75139/1000000 := by
  have ht := log_lower (by norm_num : (1:ℝ) ≤ 5000/4469)
  have hu := actual_upper
  have hr := remainder_bounds.2
  refine ⟨?_,SixthExactEnvelopeGap.actual_target_bounds.2⟩
  unfold upperRemainder AnalyticTotalThreshold.target at *
  linarith only [ht,hu,hr]

/-- The improved certificates still straddle the actual target; no direction is claimed. -/
theorem rational_endpoints_straddle :
    GlobalLogRelationPayment.lowerRational < 8*lowerLog (5000/4469) ∧
    8*V (5000/4469) < upperRational := by
  refine ⟨SixthExactEnvelopeGap.rational_endpoints_straddle.1,?_⟩
  rw [upper_exact]
  norm_num [V,upperLog,lowerLog]

end
end Wu2008DoubleSieve.FourMovingLogChord
