import TightActualQComparison

namespace Wu2008DoubleSieve.ExactWeightTripleEnclosure
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure (a s)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)
open BaseGSharedActualRecovery
open JointSharedTightEnclosure (weighted weighted_integrable middleLo middleHi)
open scoped Interval
noncomputable section

/-- Exact partial fractions for the complete signed weight, degree at most three. -/
def poly (A B C D t : ℝ) : ℝ := A+B*t+C*t^2+D*t^3
def algebraic (B C D t : ℝ) : ℝ :=
  (24*B+4*C+2*D)*t+(12*C+2*D)*t^2+8*D*t^3
def primitive (A B C D t : ℝ) : ℝ :=
  16*A*log t+8*poly A B C D (1/2)*log (1/2-t)+algebraic B C D t

theorem primitive_derivative (A B C D t : ℝ) (ht : t ≠ 0) (hh : 1/2-t ≠ 0) :
    HasDerivAt (primitive A B C D)
      (SharedRationalEnvelope.weight t*poly A B C D t) t := by
  have hd := ((hasDerivAt_const t (1/2:ℝ)).sub (hasDerivAt_id t)).log hh
  convert! (((hasDerivAt_log ht).const_mul (16*A)).add
    (hd.const_mul (8*poly A B C D (1/2)))).add
    ((((hasDerivAt_id t).const_mul (24*B+4*C+2*D)).add
      (((hasDerivAt_id t).pow 2).const_mul (12*C+2*D))).add
      (((hasDerivAt_id t).pow 3).const_mul (8*D))) using 1
  dsimp [SharedRationalEnvelope.weight,poly]
  have hn : 1-t*2 ≠ 0 := by intro he; apply hh; linarith
  field_simp [ht,hh,hn]
  ring

def payment (A B C D l r : ℝ) : ℝ :=
  16*A*log (r/l)-8*poly A B C D (1/2)*log ((1/2-l)/(1/2-r))+
    algebraic B C D r-algebraic B C D l

theorem full_ftc (A B C D l r : ℝ) (hl : 0 < l) (hr : r < 1/2) (ho : l ≤ r) :
    (∫ t in l..r, SharedRationalEnvelope.weight t*poly A B C D t) =
      payment A B C D l r := by
  have geom (t : ℝ) (ht : t ∈ uIcc l r) : t ≠ 0 ∧ 1/2-t ≠ 0 := by
    rw [uIcc_of_le ho] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hi : IntervalIntegrable (fun t => SharedRationalEnvelope.weight t*poly A B C D t) volume l r := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · unfold SharedRationalEnvelope.weight
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t ht; exact mul_ne_zero (geom t ht).1 (geom t ht).2
    · unfold poly; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => primitive_derivative A B C D t (geom t ht).1 (geom t ht).2) hi]
  unfold primitive payment
  rw [log_div (by linarith : r ≠ 0) hl.ne',
    log_div (by linarith : 1/2-l ≠ 0) (by linarith : 1/2-r ≠ 0)]
  ring

/-- Original polynomial in the affine recurrence coordinate, with no new cuts. -/
def shifted (j A B C D t : ℝ) : ℝ :=
  poly A B C D (u t-j)
def tA (j A B C D : ℝ) : ℝ := poly A B C D (1/(2*a)-j)
def tB (j B C D : ℝ) : ℝ := -(B+2*C*(1/(2*a)-j)+3*D*(1/(2*a)-j)^2)/a
def tC (j C D : ℝ) : ℝ := (C+3*D*(1/(2*a)-j))/a^2
def tD (D : ℝ) : ℝ := -D/a^3

theorem shifted_eq (j A B C D t : ℝ) : shifted j A B C D t =
    poly (tA j A B C D) (tB j B C D) (tC j C D) (tD D) t := by
  dsimp [shifted, tA, tB, tC, tD, poly, u]
  field_simp [truncatedSixthLower_parameters.1.ne']
  ring

def pay (j A B C D l r : ℝ) : ℝ :=
  payment (tA j A B C D) (tB j B C D) (tC j C D) (tD D) l r

theorem shifted_ftc (j A B C D l r : ℝ) (hl : 0 < l) (hr : r < 1/2) (ho : l ≤ r) :
    (∫ t in l..r, SharedRationalEnvelope.weight t*shifted j A B C D t) =
      pay j A B C D l r := by
  simp_rw [shifted_eq]
  exact full_ftc _ _ _ _ _ _ hl hr ho


def highLo (v : ℝ) : ℝ := (1845671/520931250)*v/5
def highHi (v : ℝ) : ℝ := 65413/10418625+(1183/151875)*(v-5)
def highLower : ℝ := pay 0 0 ((1845671/520931250)/5) 0 0 a (c 5)
def highUpper : ℝ := pay 5 (65413/10418625) (1183/151875) 0 0 a (c 5)
def middleLower : ℝ := pay 4 (GConvexChord.r4-287/250)
  ((GConvexChord.r5-9044059/6431250)-(GConvexChord.r4-287/250)+1/144) (-1/144) 0 (c 5) (c 4)
def middleUpper : ℝ := pay 4 (GConvexChord.r4-34832/30375)
  ((GConvexChord.r5-541588/385875)-(GConvexChord.r4-34832/30375)+1/22) (-1/22) 0 (c 5) (c 4)
def lowUpper : ℝ := pay 3 0 0 0 (1/108) (c 4) s

theorem high_full_weight : weighted highLo a (c 5) ≤ highKernel ∧
    highKernel ≤ weighted highHi a (c 5) := by
  have ho : a ≤ c 5 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hs : c 5 ≤ s := by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hi := kernel_integrable (fun v => (42823/151875)*v) le_rfl hs ho (by fun_prop)
  have hl := weighted_integrable highLo (by unfold highLo; fun_prop) le_rfl hs ho
  have hh := weighted_integrable highHi (by unfold highHi; fun_prop) le_rfl hs ho
  constructor
  · apply intervalIntegral.integral_mono_on ho hl hi
    intro t ht
    have hg := HighSharedKernelMagnitude.high_geometry ht
    have ha := SharpSingleBalance.upper_ratio_antitone (by norm_num : (0:ℝ)<5) hg.2.2.1
    have h5 := HighSharedKernelMagnitude.upper_five_sandwich.2
    have hv0 : 0 < u t := by linarith only [hg.2.2.1]
    have ha' := (div_le_iff₀ hv0).1 (ha.trans (div_le_div_of_nonneg_right h5 (by norm_num)))
    rw [HighSharedKernelMagnitude.kernel_density]
    apply mul_le_mul_of_nonneg_left _ (by linarith only [(HighSharedKernelMagnitude.high_weight ht).1])
    unfold highLo; linarith only [ha']
  · apply intervalIntegral.integral_mono_on ho hi hh
    intro t ht
    have hg := HighSharedKernelMagnitude.high_geometry ht
    rw [HighSharedKernelMagnitude.kernel_density]
    exact mul_le_mul_of_nonneg_left (HighSharedKernelMagnitude.high_pointwise hg.2.2.1 hg.2.2.2).2
      (by linarith only [(HighSharedKernelMagnitude.high_weight ht).1])

theorem window_payments : highLower ≤ highKernel ∧ highKernel ≤ highUpper ∧
    middleLower ≤ middleKernel ∧ middleKernel ≤ middleUpper ∧ lowKernel ≤ lowUpper := by
  have ehL : weighted highLo a (c 5) = highLower := by
    unfold weighted highLower
    rw [← shifted_ftc _ _ _ _ _ _ _ truncatedSixthLower_parameters.1
      (by norm_num [c,a,truncatedSixthLowerAlpha]) (by norm_num [c,a,truncatedSixthLowerAlpha])]
    apply intervalIntegral.integral_congr
    intro t ht; dsimp [highLo,shifted,poly]; ring
  have ehH : weighted highHi a (c 5) = highUpper := by
    unfold weighted highUpper
    rw [← shifted_ftc _ _ _ _ _ _ _ truncatedSixthLower_parameters.1
      (by norm_num [c,a,truncatedSixthLowerAlpha]) (by norm_num [c,a,truncatedSixthLowerAlpha])]
    apply intervalIntegral.integral_congr
    intro t ht; dsimp [highHi,shifted,poly]; ring
  have emL : weighted middleLo (c 5) (c 4) = middleLower := by
    unfold weighted middleLower
    rw [← shifted_ftc _ _ _ _ _ _ _ (by norm_num [c,a,truncatedSixthLowerAlpha])
      (by norm_num [c,a,truncatedSixthLowerAlpha]) (by norm_num [c,a,truncatedSixthLowerAlpha])]
    apply intervalIntegral.integral_congr
    intro t ht; dsimp [middleLo,shifted,poly]; ring
  have emH : weighted middleHi (c 5) (c 4) = middleUpper := by
    unfold weighted middleUpper
    rw [← shifted_ftc _ _ _ _ _ _ _ (by norm_num [c,a,truncatedSixthLowerAlpha])
      (by norm_num [c,a,truncatedSixthLowerAlpha]) (by norm_num [c,a,truncatedSixthLowerAlpha])]
    apply intervalIntegral.integral_congr
    intro t ht; dsimp [middleHi,shifted,poly]; ring
  have elH : weighted (fun v => (v-3)^3/108) (c 4) s = lowUpper := by
    unfold weighted lowUpper
    rw [← shifted_ftc _ _ _ _ _ _ _ (by norm_num [c,a,truncatedSixthLowerAlpha])
      (by norm_num [s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
      SharedRationalEnvelope.window_order.2.1]
    apply intervalIntegral.integral_congr
    intro t ht; dsimp [shifted,poly]; ring
  have hh := high_full_weight
  have hm := JointSharedTightEnclosure.middle_full_weight_enclosure
  have hl := JointSharedTightEnclosure.low_full_weight_enclosure.2
  rw [ehL,ehH] at hh
  rw [emL,emH] at hm
  rw [elH] at hl
  exact ⟨hh.1,hh.2,hm.1,hm.2,hl⟩

/-- Endpoint logs collected with g before any envelope is spent. -/
def lowerEnvelope (L H : ℝ → ℝ) : ℝ :=
  489733639137290807553949/14295164351006756250000+
  (-12001466293/401953125)*H (327/200)+
  (-50995965659/1715000000)*H (527/327)+
  (-28876817/6000000)*H (727/527)+
  (-8)*H (1200/727)+
  (278805986/260465625)*L (5/4)

theorem lower_joint_identity : gLogRemainder+highLower+middleLower = lowerEnvelope log log := by
  norm_num [gLogRemainder,highLower,middleLower,lowerEnvelope,pay,payment,tA,tB,tC,tD,poly,algebraic,
    a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma,GConvexChord.C,GConvexChord.m,
    GConvexChord.r4,GConvexChord.r5,VariableGIntegral.logCoefficient,VariableGIntegral.a,upperLog]
  ring

/-- Endpoint logs collected with g before any envelope is spent. -/
def upperEnvelope (L H : ℝ → ℝ) : ℝ :=
  38230927760719709892132667/1225810343098829348437500+
  (-857478224/28940625)*L (327/200)+
  (-49368190687/1528065000)*L (527/327)+
  (12434923/5400000)*H (727/527)+
  (-8)*L (1200/727)+
  (907616/3472875)*H (1127/1000)+
  (833047316/114604875)*H (5/4)+
  (2)*H (4/3)

theorem upper_joint_identity : gLogRemainder+highUpper+middleUpper+lowUpper = upperEnvelope log log := by
  norm_num [gLogRemainder,highUpper,middleUpper,lowUpper,upperEnvelope,pay,payment,tA,tB,tC,tD,poly,algebraic,
    a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma,GConvexChord.C,GConvexChord.m,
    GConvexChord.r4,GConvexChord.r5,VariableGIntegral.logCoefficient,VariableGIntegral.a,upperLog]
  ring

def lowerBound : ℝ := lowerEnvelope lowerLog JointLogTotalComparison.V
def upperBound : ℝ := JointSharedTightEnclosure.baseUpperPayment+
  upperEnvelope lowerLog JointLogTotalComparison.V

theorem joint_log_payment : lowerBound ≤ lowerEnvelope log log ∧
    upperEnvelope log log ≤ upperEnvelope lowerLog JointLogTotalComparison.V := by
  have l0 := log_lower (by norm_num : (1:ℝ) ≤ 327/200)
  have h0 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 327/200)
  have l1 := log_lower (by norm_num : (1:ℝ) ≤ 527/327)
  have h1 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 527/327)
  have l2 := log_lower (by norm_num : (1:ℝ) ≤ 727/527)
  have h2 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 727/527)
  have l3 := log_lower (by norm_num : (1:ℝ) ≤ 1200/727)
  have h3 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 1200/727)
  have l4 := log_lower (by norm_num : (1:ℝ) ≤ 1127/1000)
  have h4 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 1127/1000)
  have l5 := log_lower (by norm_num : (1:ℝ) ≤ 5/4)
  have h5 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 5/4)
  have l6 := log_lower (by norm_num : (1:ℝ) ≤ 4/3)
  have h6 := JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 4/3)
  unfold lowerBound lowerEnvelope upperEnvelope
  constructor <;> linarith only [l0,h0,l1,h1,l2,h2,l3,h3,l4,h4,l5,h5,l6,h6]

/-- Each constituent is consumed once, and only after logarithmic coefficients are collected. -/
theorem triple_payments : lowerBound ≤ JointSharedTightEnclosure.triple ∧
    JointSharedTightEnclosure.triple ≤ upperBound := by
  have hw := window_payments
  have hb := AnalyticTotalThreshold.signed_losses_nonnegative.1
  have hbu := JointSharedTightEnclosure.base_payment
  have hl := low_nonnegative
  have hg := g_exact
  have el := lower_joint_identity
  have eh := upper_joint_identity
  have hp := joint_log_payment
  unfold JointSharedTightEnclosure.triple
  rw [shared_exact]
  unfold upperBound
  constructor <;> linarith only [hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2,
    hb,hbu,hl,hg,el,eh,hp.1,hp.2]

theorem rational_bounds : (6928/100000:ℝ) < lowerBound ∧ upperBound < 19064/100000 := by
  norm_num [lowerBound,upperBound,lowerEnvelope,upperEnvelope,
    JointSharedTightEnclosure.baseUpperPayment,JointLogTotalComparison.V,lowerLog,upperLog]

theorem triple_magnitude : (6928/100000:ℝ) < JointSharedTightEnclosure.triple ∧
    JointSharedTightEnclosure.triple < 19064/100000 :=
  ⟨rational_bounds.1.trans_le triple_payments.1,triple_payments.2.trans_lt rational_bounds.2⟩

/-- Absolute endpoints for the actual coefficient, including all remaining errors. -/
def actualLower : ℝ := JointSixthFourDiagnostic.coefficient+
  (FifthActualIntegralRecovery.recovery+lowerBound)/4
def actualUpper : ℝ := JointSixthFourDiagnostic.coefficient+
  (FifthActualIntegralRecovery.recovery+upperBound)/4+4409/200000

theorem actual_Q_enclosure : actualLower ≤ JointHMotherPayment.unroundedCoefficient ∧
    JointHMotherPayment.unroundedCoefficient < actualUpper := by
  have ht := triple_payments
  have hq := TightActualQComparison.actual_error_interval
  unfold actualLower actualUpper
  unfold JointSharedTightEnclosure.coefficient at hq
  constructor <;> linarith only [ht.1,ht.2,hq.1,hq.2]

def targetFloor : ℝ := 7/50-1/200-1/20-1/100-1/100000-1/100000-
  7/400-FourActualCapRecovery.recovery/4-(9007/100000)/4-upperBound/4-4409/200000

def targetCeiling : ℝ := 3/20-3/10000-FourActualCapRecovery.recovery/4-
  (2539/100000)/4-lowerBound/4

/-- Reconsume the full actual-Q ledger, not a subtraction from an old bound. -/
theorem actual_target_difference :
    targetFloor < AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient < targetCeiling := by
  have he := JointSharedTightEnclosure.target_exact_difference
  have hq := TightActualQComparison.actual_error_interval
  have hd : (7/50:ℝ) < JointLogTotalComparison.rationalDeficit ∧
      JointLogTotalComparison.rationalDeficit < 3/20 := by
    norm_num [JointLogTotalComparison.rationalDeficit]
  have hp := PsiG18Strength.two_recoveries_bounds
  have hl := SixthLogTotalMagnitude.log_remainder_cap
  have hj := SixthLogTotalMagnitude.jextra_bounds
  have ht := SixthLogTotalMagnitude.target_slack_bounds
  have hs := SixthLogTotalMagnitude.square_bounds
  have h6n := SixthFullRationalEnclosure.sixth_log_loss_enclosure.1
  have h6u := SixthFullRationalEnclosure.sixth_log_loss_lt
  have h5 := FifthLogTotalMagnitude.recovery_decimal_rational_bounds
  have hb := triple_payments
  unfold targetFloor targetCeiling
  constructor <;> linarith only [he,hq.1,hq.2,hd.1,hd.2,hp.1,hp.2,hl.1,hl.2,hj.1,hj.2,
    ht.1,ht.2,hs.1,hs.2,h6n,h6u,h5.1,h5.2,hb.1,hb.2]

/-- The improvement is strict and absolute; these resulting endpoints still cross zero. -/
theorem improvement_and_remaining_sign :
    (652/10000:ℝ) < lowerBound ∧ upperBound < (17/20)*(2258/10000) ∧
    TightActualQComparison.floor < targetFloor ∧ targetCeiling < TightActualQComparison.ceiling ∧
    targetFloor < 0 ∧ 0 < targetCeiling := by
  norm_num [lowerBound,upperBound,lowerEnvelope,upperEnvelope,
    JointSharedTightEnclosure.baseUpperPayment,JointLogTotalComparison.V,lowerLog,upperLog,
    targetFloor,targetCeiling,TightActualQComparison.floor,TightActualQComparison.ceiling,
    FourActualCapRecovery.recovery_exact]

end
end Wu2008DoubleSieve.ExactWeightTripleEnclosure
