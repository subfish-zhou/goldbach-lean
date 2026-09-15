import U8ActualThreshold

/-! Signed slack ledger for the actual old coefficient. No endpoint is changed. -/
noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve
namespace GlobalLowerSlack
open ClassicalAnalyticLeaves
open FixedCoefficientUpperEnclosure (a b)
open SharpLogRecurrence (lowerLog)
open JointLogTotalComparison (V)

def fifthFloor : ℝ := FifthLogTotalMagnitude.endpoint
  (FifthLogTotalMagnitude.f0/a) (FifthLogTotalMagnitude.slope/a^2)
def fifthLogSlack : ℝ := FifthActualIntegralRecovery.logIntegral-fifthFloor
def fifthRecurrence : ℝ := fifthPairFlin-FifthActualIntegralRecovery.logIntegral
def sixthLogSlack : ℝ := ClassicalLossBottleneck.sixthLogIntegral-AnalyticTotalThreshold.sixthEndpoint
def sixthRecurrence : ℝ := truncatedSixthLowerF6lin-ClassicalLossBottleneck.sixthLogIntegral
def jSlack : ℝ := AnalyticTotalThreshold.jLoss-JointJLossStrength.recovery
def jPaymentSlack : ℝ := JointJLossStrength.recovery-JointJLossStrength.fixedRecovery
def fourSlack : ℝ := AnalyticTotalThreshold.fourLoss-FourActualCapRecovery.recovery
def highSlack : ℝ := BaseGSharedActualRecovery.highKernel-ExactWeightTripleEnclosure.highLower
def middleSlack : ℝ := BaseGSharedActualRecovery.middleKernel-ExactWeightTripleEnclosure.middleLower
/-- The G log payment is already collected with high and middle; it is not lost again. -/
def realSlack : ℝ := AnalyticTotalThreshold.baseLoss+highSlack+middleSlack+
  BaseGSharedActualRecovery.lowKernel+jSlack+jPaymentSlack+fifthLogSlack+fifthRecurrence+
  sixthLogSlack+sixthRecurrence+fourSlack

theorem triple_identity : JointSharedTightEnclosure.triple-
    ExactWeightTripleEnclosure.lowerEnvelope log log =
      AnalyticTotalThreshold.baseLoss+highSlack+middleSlack+BaseGSharedActualRecovery.lowKernel := by
  have he := ExactWeightTripleEnclosure.lower_joint_identity
  unfold JointSharedTightEnclosure.triple highSlack middleSlack
  rw [BaseGSharedActualRecovery.shared_exact,BaseGSharedActualRecovery.g_exact]
  linarith only [he]

theorem actual_minus_lowerReal : JointHMotherPayment.unroundedCoefficient-
    GlobalSignedActualComparison.lowerReal = realSlack/4 := by
  rw [GlobalSignedActualComparison.cancelled_actual_identity]
  have ht := triple_identity
  unfold GlobalSignedActualComparison.lowerReal GlobalSignedActualComparison.lowerPacket
    GlobalSignedActualComparison.mainLogs JointLogTotalComparison.logTotal TotalEndpointComparison.D
    realSlack fifthLogSlack fifthRecurrence sixthLogSlack sixthRecurrence jSlack jPaymentSlack fourSlack
    fifthFloor FifthLogTotalMagnitude.endpoint AnalyticTotalThreshold.fifthEndpoint at *
  rw [← log_div (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [a,truncatedSixthLowerAlpha])]
  rw [GlobalSignedActualComparison.log_two]
  linarith only [ht]

theorem component_nonnegative :
    0 ≤ AnalyticTotalThreshold.baseLoss ∧ 0 ≤ highSlack ∧ 0 ≤ middleSlack ∧
    0 ≤ BaseGSharedActualRecovery.lowKernel ∧ 0 ≤ jSlack ∧ 0 ≤ jPaymentSlack ∧
    0 ≤ fifthLogSlack ∧ 0 ≤ fifthRecurrence ∧ 0 ≤ sixthLogSlack ∧
    0 ≤ sixthRecurrence ∧ 0 ≤ fourSlack := by
  refine ⟨AnalyticTotalThreshold.signed_losses_nonnegative.1,?_,?_,
    BaseGSharedActualRecovery.low_nonnegative,?_,?_,?_,?_,?_,?_,?_⟩
  · exact sub_nonneg.mpr ExactWeightTripleEnclosure.window_payments.1
  · exact sub_nonneg.mpr ExactWeightTripleEnclosure.window_payments.2.2.1
  · exact sub_nonneg.mpr JointJLossStrength.actual_jLoss_lower
  · exact sub_nonneg.mpr JointJLossStrength.fixedRecovery_le_recovery
  · exact sub_nonneg.mpr FifthLogTotalMagnitude.integral_bounds.1
  · exact FifthActualIntegralRecovery.integral_distance.1
  · exact sub_nonneg.mpr ClassicalLossBottleneck.sixth_endpoint_le_logIntegral
  · exact ClassicalLossBottleneck.sixth_recurrence_integral_cap.1
  · exact sub_nonneg.mpr FourActualCapRecovery.actual_fourLoss_lower

/-- Signed whole-packet rounding, after the already frozen zero relation. -/
def analyticPaymentSlack : ℝ := GlobalSignedActualComparison.lowerCollected log log-
  GlobalLogRelationPayment.lowerRepaid lowerLog V
def retainedPaymentSlack : ℝ := Phase18.g18+Phase20.psiPaymentLoss-3/10000

theorem actual_minus_lowerRational : JointHMotherPayment.unroundedCoefficient-
    GlobalLogRelationPayment.lowerRational =
      (realSlack+analyticPaymentSlack)/4+retainedPaymentSlack := by
  have he := actual_minus_lowerReal
  have hr := JointLogTotalComparison.fixedCertificate_exact
  unfold JointLogTotalComparison.fixedCertificate JointLogTotalComparison.classicalPayment at hr
  unfold GlobalSignedActualComparison.lowerReal at he
  rw [GlobalSignedActualComparison.lower_collection] at he
  unfold GlobalLogRelationPayment.lowerRational GlobalSignedActualComparison.lowerRational
    GlobalLogRelationPayment.lowerGain analyticPaymentSlack retainedPaymentSlack
    JointLogTotalComparison.retainedExtra Phase20.psiPaymentLoss at *
  linarith only [he,hr]

theorem payment_nonnegative : 0 ≤ analyticPaymentSlack ∧ 0 < retainedPaymentSlack :=
  ⟨sub_nonneg.mpr GlobalLogRelationPayment.lower_repaid_payment,
    sub_pos.mpr PsiG18Strength.two_recoveries_bounds.1⟩

/-- The old lower proof dropped this exact reciprocal-chord term. -/
theorem scalar_chord_retained {z : ℝ} (hz : SharpMassBalance.s0 ≤ z)
    (hq : z ≤ FifthClassicalShape.q) :
    FifthLogTotalMagnitude.f0+FifthLogTotalMagnitude.slope*(z-SharpMassBalance.s0)+
      (FifthLogTotalMagnitude.slope/FifthClassicalShape.q)*(z-SharpMassBalance.s0)*
        (FifthClassicalShape.q-z) ≤ log (z-1)/z := by
  have hp := FifthClassicalShape.parameters
  have hs : 0 < SharpMassBalance.s0 := by linarith [hp.1]
  have hz0 := hs.trans_le hz
  have hq0 := hs.trans hp.2.1
  have hd := sub_pos.mpr hp.2.1
  have hL := (FifthLogTotalMagnitude.endpoint_logs hp.1.le).1
  have hQ := (FifthLogTotalMagnitude.endpoint_logs
    (show 3 ≤ FifthClassicalShape.q by linarith [hp.1,hp.2.1])).1
  have hc := FifthLogTotalMagnitude.log_chord
    (show 0 < SharpMassBalance.s0-1 by linarith [hp.1])
    (show SharpMassBalance.s0-1 ≤ z-1 by linarith)
    (show z-1 ≤ FifthClassicalShape.q-1 by linarith)
    (show SharpMassBalance.s0-1 < FifthClassicalShape.q-1 by linarith [hp.2.1])
  have h1 := mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr hq)
  have h2 := mul_le_mul_of_nonneg_left hQ (sub_nonneg.mpr hz)
  have hch : ((FifthClassicalShape.q-z)*FifthLogTotalMagnitude.lo SharpMassBalance.s0+
      (z-SharpMassBalance.s0)*FifthLogTotalMagnitude.lo FifthClassicalShape.q)/
      (FifthClassicalShape.q-SharpMassBalance.s0) ≤ log (z-1) := by
    apply (div_le_iff₀ hd).2
    have hc' := (div_le_iff₀
      (show 0 < (FifthClassicalShape.q-1)-(SharpMassBalance.s0-1) by linarith)).1 hc
    nlinarith only [h1,h2,hc']
  have hid : (((FifthClassicalShape.q-z)*FifthLogTotalMagnitude.lo SharpMassBalance.s0+
      (z-SharpMassBalance.s0)*FifthLogTotalMagnitude.lo FifthClassicalShape.q)/
      (FifthClassicalShape.q-SharpMassBalance.s0))/z =
      FifthLogTotalMagnitude.f0+FifthLogTotalMagnitude.slope*(z-SharpMassBalance.s0)+
      FifthLogTotalMagnitude.slope*(z-SharpMassBalance.s0)*(FifthClassicalShape.q-z)/z := by
    unfold FifthLogTotalMagnitude.slope FifthLogTotalMagnitude.f0
    field_simp
    ring
  have hl := div_le_div_of_nonneg_right hch hz0.le
  rw [hid] at hl
  have hslope : 0 ≤ FifthLogTotalMagnitude.slope := by
    norm_num [FifthLogTotalMagnitude.slope,FifthLogTotalMagnitude.f0,FifthLogTotalMagnitude.lo,
      FifthClassicalShape.q,SharpMassBalance.s0,lowerLog,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have hn := mul_nonneg (mul_nonneg hslope (sub_nonneg.mpr hz)) (sub_nonneg.mpr hq)
  have hm := div_le_div_of_nonneg_left hn hz0 hq
  have he : FifthLogTotalMagnitude.slope/FifthClassicalShape.q*(z-SharpMassBalance.s0)*
      (FifthClassicalShape.q-z) = FifthLogTotalMagnitude.slope*(z-SharpMassBalance.s0)*
        (FifthClassicalShape.q-z)/FifthClassicalShape.q := by ring
  rw [he]
  linarith only [hl,hm]

/-- Uniform curvature on the original interval, not a Taylor truncation. -/
theorem log_strong_chord {l t r : ℝ} (hl : 0 < l) (hlt : l ≤ t)
    (htr : t ≤ r) (hlr : l < r) :
    ((r-t)*log l+(t-l)*log r)/(r-l)+(t-l)*(r-t)/(2*r^2) ≤ log t := by
  have hr : 0 < r := hl.trans hlr
  have hrl : r-l ≠ 0 := (sub_pos.mpr hlr).ne'
  let F : ℝ → ℝ := fun x => log x+x^2/(2*r^2)
  have hd (x : ℝ) (hx : x ∈ Icc l r) : HasDerivAt F (1/x+x/r^2) x := by
    convert (hasDerivAt_log (hl.trans_le hx.1).ne').add
      (((hasDerivAt_id x).pow 2).div_const (2*r^2)) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hc : ConcaveOn ℝ (Icc l r) F := by
    apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx y hy hxy
      have hx' := interior_subset hx
      have hy' := interior_subset hy
      rw [(hd x hx').deriv,(hd y hy').deriv]
      have hx0 := hl.trans_le hx'.1
      have hy0 := hl.trans_le hy'.1
      have hprod : x*y ≤ r^2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hx'.2) hy0.le,
          mul_nonneg (sub_nonneg.mpr hy'.2) hr.le]
      have hm := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) (mul_pos hx0 hy0) hprod
      have he : (1/x+x/r^2)-(1/y+y/r^2) = (y-x)/(x*y)-(y-x)/r^2 := by
        field_simp; ring
      linarith only [hm,he]
  have ha : 0 ≤ (r-t)/(r-l) := div_nonneg (sub_nonneg.mpr htr) (sub_pos.mpr hlr).le
  have hb : 0 ≤ (t-l)/(r-l) := div_nonneg (sub_nonneg.mpr hlt) (sub_pos.mpr hlr).le
  have hab : (r-t)/(r-l)+(t-l)/(r-l)=1 := by field_simp [hrl]; ring
  have hc' := hc.2 (show l ∈ Icc l r from ⟨le_rfl,hlr.le⟩)
    (show r ∈ Icc l r from ⟨hlr.le,le_rfl⟩) ha hb hab
  have he : (r-t)/(r-l)*l+(t-l)/(r-l)*r=t := by field_simp [hrl]; ring
  simp only [smul_eq_mul,he] at hc'
  have hid : (r-t)/(r-l)*F l+(t-l)/(r-l)*F r =
      ((r-t)*log l+(t-l)*log r)/(r-l)+(t-l)*(r-t)/(2*r^2)+t^2/(2*r^2) := by
    dsimp [F]; field_simp [hrl]; ring
  rw [hid] at hc'
  dsimp [F] at hc'
  linarith only [hc']

def scalarRate : ℝ := (FifthLogTotalMagnitude.slope+1/(2*(FifthClassicalShape.q-1)^2))/FifthClassicalShape.q

theorem scalarRate_pos : 0 < scalarRate := by
  norm_num [scalarRate,FifthLogTotalMagnitude.slope,FifthLogTotalMagnitude.f0,FifthLogTotalMagnitude.lo,
    FifthClassicalShape.q,SharpMassBalance.s0,lowerLog,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

/-- Both the reciprocal chord gap and the uniform log curvature are retained. -/
theorem scalar_joint_gain {z : ℝ} (hz : SharpMassBalance.s0 ≤ z)
    (hq : z ≤ FifthClassicalShape.q) :
    FifthLogTotalMagnitude.f0+FifthLogTotalMagnitude.slope*(z-SharpMassBalance.s0)+
      scalarRate*(z-SharpMassBalance.s0)*(FifthClassicalShape.q-z) ≤ log (z-1)/z := by
  have hp := FifthClassicalShape.parameters
  have hs : 0 < SharpMassBalance.s0 := by linarith [hp.1]
  have hz0 := hs.trans_le hz
  have hq0 := hs.trans hp.2.1
  have hd := sub_pos.mpr hp.2.1
  have hL := (FifthLogTotalMagnitude.endpoint_logs hp.1.le).1
  have hQ := (FifthLogTotalMagnitude.endpoint_logs
    (show 3 ≤ FifthClassicalShape.q by linarith [hp.1,hp.2.1])).1
  have hc := log_strong_chord (show 0 < SharpMassBalance.s0-1 by linarith [hp.1])
    (show SharpMassBalance.s0-1 ≤ z-1 by linarith)
    (show z-1 ≤ FifthClassicalShape.q-1 by linarith)
    (show SharpMassBalance.s0-1 < FifthClassicalShape.q-1 by linarith [hp.2.1])
  have hc' : ((FifthClassicalShape.q-z)*log (SharpMassBalance.s0-1)+
      (z-SharpMassBalance.s0)*log (FifthClassicalShape.q-1))/(FifthClassicalShape.q-SharpMassBalance.s0)+
      (z-SharpMassBalance.s0)*(FifthClassicalShape.q-z)/(2*(FifthClassicalShape.q-1)^2) ≤ log (z-1) := by
    convert hc using 1; ring
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr hq))
    (mul_le_mul_of_nonneg_left hQ (sub_nonneg.mpr hz))
  have hh' := div_le_div_of_nonneg_right hh hd.le
  have hc'' := add_le_add hh' (le_refl ((z-SharpMassBalance.s0)*(FifthClassicalShape.q-z)/(2*(FifthClassicalShape.q-1)^2)))
  have hl := div_le_div_of_nonneg_right (hc''.trans hc') hz0.le
  have hid : (((FifthClassicalShape.q-z)*FifthLogTotalMagnitude.lo SharpMassBalance.s0+
      (z-SharpMassBalance.s0)*FifthLogTotalMagnitude.lo FifthClassicalShape.q)/
      (FifthClassicalShape.q-SharpMassBalance.s0)+
      (z-SharpMassBalance.s0)*(FifthClassicalShape.q-z)/(2*(FifthClassicalShape.q-1)^2))/z =
    FifthLogTotalMagnitude.f0+FifthLogTotalMagnitude.slope*(z-SharpMassBalance.s0)+
      (FifthLogTotalMagnitude.slope+1/(2*(FifthClassicalShape.q-1)^2))*
      (z-SharpMassBalance.s0)*(FifthClassicalShape.q-z)/z := by
    unfold FifthLogTotalMagnitude.slope FifthLogTotalMagnitude.f0
    field_simp; ring
  rw [hid] at hl
  have hn : 0 ≤ (FifthLogTotalMagnitude.slope+1/(2*(FifthClassicalShape.q-1)^2))*
      (z-SharpMassBalance.s0)*(FifthClassicalShape.q-z) := by
    have hr : 0 < FifthLogTotalMagnitude.slope+1/(2*(FifthClassicalShape.q-1)^2) :=
      (div_pos_iff_of_pos_right hq0).mp scalarRate_pos
    exact mul_nonneg (mul_nonneg hr.le (sub_nonneg.mpr hz)) (sub_nonneg.mpr hq)
  have hm := div_le_div_of_nonneg_left hn hz0 hq
  have he : scalarRate*(z-SharpMassBalance.s0)*(FifthClassicalShape.q-z) =
      (FifthLogTotalMagnitude.slope+1/(2*(FifthClassicalShape.q-1)^2))*
      (z-SharpMassBalance.s0)*(FifthClassicalShape.q-z)/FifthClassicalShape.q := by unfold scalarRate; ring
  rw [he]
  linarith only [hl,hm]

def densityRate : ℝ := scalarRate/(a^3*b^2)
def gainDensity (x y : ℝ) : ℝ := densityRate*(2*b-x-y)*(x+y-2*a)
def innerPoly (y : ℝ) : ℝ := densityRate*((2*b-y)*(y-2*a)*(y-a)+
  (2*b+2*a-2*y)*(y^2-a^2)/2-(y^3-a^3)/3)
def outerPoly (y : ℝ) : ℝ := densityRate*(-7*y^4/12+(b+4*a/3)*y^3-
  (a^2/2+3*a*b)*y^2+(3*a^2*b-2*a^3/3)*y)
def fifthGain : ℝ := (5/3)*densityRate*(b-a)^4

theorem kernel_joint_gain {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    FifthLogTotalMagnitude.kernel (FifthLogTotalMagnitude.f0/a)
      (FifthLogTotalMagnitude.slope/a^2) x y+gainDensity x y ≤
        FifthActualIntegralRecovery.logRegular x y := by
  have ha := truncatedSixthLower_parameters.1
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hb0 := hy0.trans_le hy
  have hp := FifthActualIntegralRecovery.parameter_range hx hxy hy
  have hh := scalar_joint_gain hp.1 hp.2
  have hm := div_le_div_of_nonneg_right hh (mul_pos ha (mul_pos hx0 hy0)).le
  have hz : 0 < 1/2-x-y := by
    have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
    linarith [hxy.trans hy]
  have hn : 0 ≤ scalarRate*(2*b-x-y)*(x+y-2*a)/a^3 := by
    apply div_nonneg _ (pow_pos ha 3).le
    exact mul_nonneg (mul_nonneg scalarRate_pos.le (by linarith [hxy.trans hy])) (by linarith)
  have hd : x*y ≤ b^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hxy.trans hy)) hy0.le,
      mul_nonneg (sub_nonneg.mpr hy) hb0.le]
  have hrec := div_le_div_of_nonneg_left hn (mul_pos hx0 hy0) hd
  have he : (FifthLogTotalMagnitude.f0+FifthLogTotalMagnitude.slope*
      (truncatedSixthLowerS 0 x y-SharpMassBalance.s0)+
      scalarRate*(truncatedSixthLowerS 0 x y-SharpMassBalance.s0)*
        (FifthClassicalShape.q-truncatedSixthLowerS 0 x y))/(a*(x*y)) =
      FifthLogTotalMagnitude.kernel (FifthLogTotalMagnitude.f0/a)
        (FifthLogTotalMagnitude.slope/a^2) x y+
        (scalarRate*(2*b-x-y)*(x+y-2*a)/a^3)/(x*y) := by
    dsimp [FifthLogTotalMagnitude.kernel,SharpMassBalance.s0,FifthClassicalShape.q,
      truncatedSixthLowerS,truncatedSixthLowerC]
    field_simp; ring
  have hlog : (log (truncatedSixthLowerS 0 x y-1)/truncatedSixthLowerS 0 x y)/(a*(x*y)) =
      FifthActualIntegralRecovery.logRegular x y := by
    rw [FifthActualIntegralRecovery.log_literal hx hxy hy]
    dsimp [truncatedSixthLowerS,truncatedSixthLowerC]
    field_simp [ha.ne',hx0.ne',hy0.ne',hz.ne']; ring
  rw [he,hlog] at hm
  have hg : gainDensity x y = (scalarRate*(2*b-x-y)*(x+y-2*a)/a^3)/b^2 := by
    unfold gainDensity densityRate; ring
  rw [hg]
  linarith only [hm,hrec]

theorem innerPoly_ftc (y : ℝ) : (∫ x in a..y, gainDensity x y) = innerPoly y := by
  let P : ℝ → ℝ := fun x => densityRate*((2*b-y)*(y-2*a)*x+(2*b+2*a-2*y)*x^2/2-x^3/3)
  have hd (x : ℝ) : HasDerivAt P (gainDensity x y) x := by
    convert ((((hasDerivAt_id x).const_mul ((2*b-y)*(y-2*a))).add
      (((hasDerivAt_id x).pow 2).const_mul (2*b+2*a-2*y) |>.div_const 2)).sub
      (((hasDerivAt_id x).pow 3).div_const 3)).const_mul densityRate using 1 <;>
      first | rfl | (dsimp [gainDensity]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by unfold gainDensity; fun_prop : Continuous (fun x => gainDensity x y)).intervalIntegrable _ _)]
  dsimp [P,innerPoly]; ring

theorem fifthGain_ftc : (4:ℝ)*(∫ y in a..b, innerPoly y) = fifthGain := by
  have hd (y : ℝ) : HasDerivAt outerPoly (innerPoly y) y := by
    convert ((((((hasDerivAt_id y).pow 4).const_mul (-7/12)).add
      (((hasDerivAt_id y).pow 3).const_mul (b+4*a/3))).sub
      (((hasDerivAt_id y).pow 2).const_mul (a^2/2+3*a*b))).add
      ((hasDerivAt_id y).const_mul (3*a^2*b-2*a^3/3))).const_mul densityRate using 1 <;>
      first | rfl | (funext x; dsimp [outerPoly]; ring) | (dsimp [innerPoly]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    ((by unfold innerPoly; fun_prop : Continuous innerPoly).intervalIntegrable _ _)]
  unfold outerPoly fifthGain
  ring

/-- The genuine full old triangle is integrated; no subwindow is chosen. -/
theorem fifth_gain_paid : fifthGain ≤ fifthLogSlack := by
  let p := FifthLogTotalMagnitude.f0/a
  let k := FifthLogTotalMagnitude.slope/a^2
  have hp := truncatedSixthLower_parameters
  have hm : Continuous (fun y : ℝ => ∫ x in a..y, FifthActualIntegralRecovery.logRegular x y) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ => FifthActualIntegralRecovery.logRegular x y)
    · exact FifthActualIntegralRecovery.log_continuous.comp (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hn (y : ℝ) (hy : y ∈ uIcc a b) : y ≠ 0 := by
    rw [uIcc_of_le hp.2.1.le] at hy
    exact (hp.1.trans_le hy.1).ne'
  have hil : ContinuousOn (fun y : ℝ => log y-log a) (uIcc a b) :=
    (continuousOn_id.log (fun y hy => hn y hy)).sub continuousOn_const
  have hi : IntervalIntegrable (FifthLogTotalMagnitude.inner p k) volume a b := by
    apply ContinuousOn.intervalIntegrable
    unfold FifthLogTotalMagnitude.inner
    exact (((continuousOn_const.add (continuousOn_const.mul
      (continuousOn_const.sub continuousOn_id))).mul hil).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).div
      continuousOn_id (fun y hy => hn y hy)
  have hpi : IntervalIntegrable innerPoly volume a b :=
    (by unfold innerPoly; fun_prop : Continuous innerPoly).intervalIntegrable _ _
  have hpoint (y : ℝ) (hy : y ∈ Icc a b) : FifthLogTotalMagnitude.inner p k y+innerPoly y ≤
      ∫ x in a..y, FifthActualIntegralRecovery.logRegular x y := by
    have hik : IntervalIntegrable (fun x => FifthLogTotalMagnitude.kernel p k x y) volume a y := by
      apply ContinuousOn.intervalIntegrable
      unfold FifthLogTotalMagnitude.kernel
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro x hx
      rw [uIcc_of_le hy.1] at hx
      exact mul_ne_zero (hp.1.trans_le hx.1).ne' (hp.1.trans_le hy.1).ne'
    have hgi : IntervalIntegrable (fun x => gainDensity x y) volume a y :=
      (by unfold gainDensity; fun_prop : Continuous (fun x => gainDensity x y)).intervalIntegrable _ _
    have hcomp := intervalIntegral.integral_mono_on hy.1 (hik.add hgi)
      ((FifthActualIntegralRecovery.log_continuous.comp (f := fun x : ℝ => (x,y))
        (by fun_prop)).intervalIntegrable a y) (fun x hx => kernel_joint_gain hx.1 hx.2 hy.2)
    rw [intervalIntegral.integral_add hik hgi,FifthLogTotalMagnitude.inner_ftc p k hy.1,
      innerPoly_ftc] at hcomp
    exact hcomp
  have hh := intervalIntegral.integral_mono_on hp.2.1.le (hi.add hpi) (hm.intervalIntegrable a b) hpoint
  rw [intervalIntegral.integral_add hi hpi] at hh
  have hd (y : ℝ) (hy : y ∈ uIcc a b) := FifthLogTotalMagnitude.primitive_derivative p k
    (show a ≤ y by rw [uIcc_of_le hp.2.1.le] at hy; exact hy.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi] at hh
  have hg := fifthGain_ftc
  unfold fifthLogSlack fifthFloor FifthLogTotalMagnitude.endpoint FifthActualIntegralRecovery.logIntegral
  dsimp [FifthLogTotalMagnitude.primitive,p,k] at hh
  linarith only [hh,hg]

theorem fifthGain_pos : 0 < fifthGain := by
  unfold fifthGain densityRate
  exact mul_pos (mul_pos (by norm_num) (div_pos scalarRate_pos
    (mul_pos (pow_pos truncatedSixthLower_parameters.1 3)
      (sq_pos_of_pos (truncatedSixthLower_parameters.1.trans truncatedSixthLower_parameters.2.1)))))
    (pow_pos (sub_pos.mpr truncatedSixthLower_parameters.2.1) 4)

theorem realSlack_lower : fifthGain ≤ realSlack := by
  obtain ⟨hb,hh,hm,hl,hj,hjp,h5,h5r,h6,h6r,h4⟩ := component_nonnegative
  unfold realSlack
  linarith only [hb,hh,hm,hl,hj,hjp,h5,h5r,h6,h6r,h4,fifth_gain_paid]

def lowerOld : ℝ := GlobalLogRelationPayment.lowerRational+fifthGain/4

theorem old_actual_lower : lowerOld < JointHMotherPayment.unroundedCoefficient := by
  have he := actual_minus_lowerRational
  have hs := realSlack_lower
  have hp := payment_nonnegative
  unfold lowerOld
  linarith only [he,hs,hp.1,hp.2]

def lowerCoefficient : ℝ := U8ActualThreshold.lowerCoefficient+fifthGain/4

theorem actual_lower : lowerCoefficient < U8CanonicalMother.improvedCoefficient := by
  have ho := old_actual_lower
  have hs := FullAdmissibleStrength.polynomial_payment
  have hg := U8ActualThreshold.exact_weight_gain_bounds.1
  rw [U8ActualThreshold.actual_identity]
  unfold lowerCoefficient U8ActualThreshold.lowerCoefficient lowerOld at *
  linarith only [ho,hs,hg]

theorem strict_improvement : U8ActualThreshold.lowerCoefficient < lowerCoefficient := by
  unfold lowerCoefficient
  linarith only [fifthGain_pos]

def residual : ℝ := U8ActualThreshold.residual-fifthGain/4

theorem residual_identity : residual = 8*V (5000/4469)-lowerCoefficient := by
  rw [residual,U8ActualThreshold.residual_identity,lowerCoefficient]
  ring

theorem actual_target_residual : 8*log (5000/4469)-U8CanonicalMother.improvedCoefficient < residual := by
  have ht := JointLogTotalComparison.log_le_V (show (1:ℝ) ≤ 5000/4469 by norm_num)
  rw [residual_identity]
  linarith only [ht,actual_lower]

/-- Exact remaining actual slacks, including the once-only sixth producer correction. -/
def unpaid : ℝ := (realSlack-fifthGain+analyticPaymentSlack)/4+retainedPaymentSlack+
  (FullAdmissibleSeed.Gamma6-FullAdmissibleStrength.polynomialPayment)/4+
  (2*(U8CanonicalMother.L-U8CanonicalMother.I)-U8ActualThreshold.gainLower)

theorem actual_remaining_identity : U8CanonicalMother.improvedCoefficient-lowerCoefficient = unpaid := by
  have he := actual_minus_lowerRational
  rw [U8ActualThreshold.actual_identity]
  unfold unpaid lowerCoefficient U8ActualThreshold.lowerCoefficient
  linarith only [he]

theorem exact_target_comparison : 8*log (5000/4469) < U8CanonicalMother.improvedCoefficient ↔
    8*log (5000/4469)-lowerCoefficient < unpaid := by
  rw [← actual_remaining_identity]
  constructor <;> intro h <;> linarith only [h]

/-- Opposite evidence is about Qold only, not the corrected coefficient. -/
theorem old_actual_below_target : JointHMotherPayment.unroundedCoefficient < 8*log (5000/4469) :=
  FifthReciprocalAffineUpper.actual_below_target

/-- A consumed, eta-free theorem about the literal common ordinary-P2 count. -/
theorem strict_ordinary_P2 :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        lowerCoefficient*U8CanonicalMother.M N <
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  have hp : 0 < (U8CanonicalMother.improvedCoefficient-lowerCoefficient)/2 :=
    half_pos (sub_pos.mpr actual_lower)
  obtain ⟨δ,hδ,hδhi,T,hT,h⟩ := U8CanonicalMother.improved_ordinary_P2 _ hp
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hs : 0 < U8CanonicalMother.M N := HighSixPhase6.original_scale_positive (hT.trans hN)
  have hc : lowerCoefficient < U8CanonicalMother.improvedCoefficient-
      (U8CanonicalMother.improvedCoefficient-lowerCoefficient)/2 := by linarith only [hp]
  exact (mul_lt_mul_of_pos_right hc hs).trans_le (h N hN he)

theorem fifthGain_exact : fifthGain =
    65216423715278935221942009918380973061309825/4698842408998425198591695703938868084110462103 := by
  norm_num [fifthGain,densityRate,scalarRate,FifthLogTotalMagnitude.slope,FifthLogTotalMagnitude.f0,
    FifthLogTotalMagnitude.lo,FifthClassicalShape.q,SharpMassBalance.s0,lowerLog,a,b,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem quarter_gain_bounds : (3469/1000000:ℝ) < fifthGain/4 ∧ fifthGain/4 < 3470/1000000 := by
  rw [fifthGain_exact]; norm_num

theorem lowerOld_bounds : (826517/1000000:ℝ) < lowerOld ∧ lowerOld < 826518/1000000 := by
  unfold lowerOld
  rw [GlobalLogRelationPayment.lower_rational_exact,fifthGain_exact]
  norm_num

theorem lowerCoefficient_bounds : (831353/1000000:ℝ) < lowerCoefficient ∧
    lowerCoefficient < 831354/1000000 := by
  unfold lowerCoefficient U8ActualThreshold.lowerCoefficient
  rw [GlobalLogRelationPayment.lower_rational_exact,FullAdmissibleStrength.polynomial_payment_exact,
    U8ActualThreshold.gainLower_exact,fifthGain_exact]
  norm_num

theorem residual_bounds : (66832/1000000:ℝ) < residual ∧ residual < 66833/1000000 := by
  unfold residual U8ActualThreshold.residual
  rw [GlobalLogRelationPayment.lower_remainder_exact,FullAdmissibleStrength.polynomial_payment_exact,
    U8ActualThreshold.gainLower_exact,fifthGain_exact]
  norm_num

theorem certificate_below_target : lowerCoefficient < 8*log (5000/4469) := by
  have hl := SharpLogRecurrence.log_lower (show (1:ℝ) ≤ 5000/4469 by norm_num)
  have hc : (831354/1000000:ℝ) < 8*lowerLog (5000/4469) := by norm_num [lowerLog]
  exact lowerCoefficient_bounds.2.trans (hc.trans_le (by linarith only [hl]))

/-- The base remainder consists of fixed-log payment and an actual beta recurrence. -/
theorem base_slack_identity : AnalyticTotalThreshold.baseLoss =
    32*(log (3/2)-lowerLog (3/2))+16*(log (26/25)-lowerLog (26/25))+
      8*BaseGSharedActualRecovery.betaKernel := BaseGSharedActualRecovery.base_exact

/-- The previously discarded sixth is independent of the Gamma6 replacement. -/
theorem sixth_slack_identity : sixthLogSlack+sixthRecurrence = AnalyticTotalThreshold.sixthLoss := by
  unfold sixthLogSlack sixthRecurrence AnalyticTotalThreshold.sixthLoss
  ring

end GlobalLowerSlack
