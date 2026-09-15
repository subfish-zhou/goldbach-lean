import FourActualCapRecovery

namespace Wu2008DoubleSieve.JFourRemainingMagnitude
open Real Set MeasureTheory FourRoughClosedMass ClassicalLogFourBounds
open FourLogAffine (ell)
open scoped Interval
noncomputable section

namespace FourLower
/-- Both constants use original endpoints, not a new cut. -/
def c : ℝ := lam-beta
def A : ℝ := SharpLogRecurrence.lowerLog ((lam-alpha)/beta)+alpha/c

theorem c_pos : 0 < c := by
  norm_num [c,lam,beta,truncatedSixthLowerLambda,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

/-- Lower moving-log envelope on the complete original interval. -/
theorem moving_log_lower {z : ℝ} (hz : alpha ≤ z) (hzb : z ≤ beta) :
    log (lam-alpha)-(z-alpha)/c ≤ log (lam-z) := by
  have hc : 0 < lam-alpha := Phase24.c_pos
  have hd : 0 < lam-z := c_pos.trans_le (by dsimp [c]; linarith)
  have h := log_le_sub_one_of_pos (div_pos hc hd)
  rw [log_div hc.ne' hd.ne'] at h
  have he : (lam-alpha)/(lam-z)-1 = (z-alpha)/(lam-z) := by field_simp; ring
  rw [he] at h
  have hb := div_le_div_of_nonneg_left (sub_nonneg.mpr hz) c_pos
    (show c ≤ lam-z by dsimp [c]; linarith)
  linarith

/-- True Buchstab half bound; no normalized-sieve substitution. -/
theorem regular_lower {x y z t : ℝ}
    (hx : alpha ≤ x) (hy : alpha ≤ y) (hz : alpha ≤ z) (ht : alpha ≤ t) :
    (1/2)/(x*y^2*z*t) ≤ regularKernel x y z t := by
  have hx0 := fixed_geometry.2.1.trans_le hx
  have hy0 := fixed_geometry.2.1.trans_le hy
  have hz0 := fixed_geometry.2.1.trans_le hz
  have ht0 := fixed_geometry.2.1.trans_le ht
  have h := LiLiuPrereqBuchstab.one_half_le_buchstab
    (show (1:ℝ) ≤ max 2 (parameter x y z t) from le_trans (by norm_num) (le_max_left _ _))
  simp only [regularKernel,clip,max_eq_right hx,max_eq_right hy,max_eq_right hz,max_eq_right ht]
  exact div_le_div_of_nonneg_right h (by positivity)

theorem inner_lower {x y z : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hz : alpha ≤ z) (hzb : z ≤ beta) :
    (1/2)/(x*y^2)*((A+ell z)/z-1/c) ≤
      regularInner10 x y z+regularInner11 x y z := by
  have hx0 := fixed_geometry.2.1.trans_le hx
  have hy0 := fixed_geometry.2.1.trans_le hy
  have hz0 := fixed_geometry.2.1.trans_le hz
  have hb0 := fixed_geometry.2.1.trans_le fixed_geometry.2.2.1
  have ho : z ≤ lam-z := by linarith [fixed_geometry.2.2.2.2.2.2.1]
  rw [Phase24.inner_join]
  have h := FourPositiveLogLower.log_tail_le_integral (C := (1/2)/(x*y^2*z))
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    hz0 ho 0 (fun t ht => by
      have hh := regular_lower hx hy hz (hz.trans ht.1)
      convert hh using 1 <;> first | rfl | ring)
  norm_num only [Nat.cast_zero,zero_add,pow_one,div_one] at h
  have hl := moving_log_lower hz hzb
  have hw := SharpLogRecurrence.log_lower (t := (lam-alpha)/beta)
    (by norm_num [lam,alpha,beta,truncatedSixthLowerLambda,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  rw [log_div (show lam-alpha ≠ 0 from Phase24.c_pos.ne') hb0.ne'] at hw
  have htail : A+ell z-z/c ≤ log (lam-z)-log z := by
    dsimp [A,ell] at *
    rw [sub_div] at hl
    linarith
  have hm := mul_le_mul_of_nonneg_left htail
    (show 0 ≤ (1/2)/(x*y^2*z) by positivity)
  refine le_trans ?_ (hm.trans h)
  apply le_of_eq
  field_simp

def Z (z : ℝ) : ℝ := -A*ell z-ell z^2/2-z/c
def F (y : ℝ) : ℝ :=
  (-ell y^2/2+(1-A)*ell y+(A-1+beta/c))/y+log y/c
def H (x : ℝ) : ℝ := F beta*log x-
  (ell x^2/2+(A-2)*ell x+(3-2*A-beta/c))/x-log x^2/(2*c)

theorem ell_derivative {x : ℝ} (hx : x ≠ 0) : HasDerivAt ell (-1/x) x := by
  convert (hasDerivAt_const x (log beta)).sub (hasDerivAt_log hx) using 1 <;>
    first | rfl | ring

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

/-- Reversed FTC comparison; this is a lower bound on the actual integral. -/
theorem compare_primitive {f g P : ℝ → ℝ} {l r : ℝ} (hlr : l ≤ r)
    (hf : Continuous f) (hg : ContinuousOn g (Icc l r))
    (hd : ∀ x ∈ Icc l r, HasDerivAt P (g x) x)
    (hb : ∀ x ∈ Icc l r, g x ≤ f x) :
    P r-P l ≤ (∫ x in l..r, f x) := by
  have hi : IntervalIntegrable g volume l r := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hlr] using hg
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (uIcc_of_le hlr ▸ hx)) hi]
  exact intervalIntegral.integral_mono_on hlr hi (hf.intervalIntegrable l r) hb

theorem middle_lower {x y : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y) (hyb : y ≤ beta) :
    (1/2)/x*((A*ell y+ell y^2/2-(beta-y)/c)/y^2) ≤
      regularMiddle10 x y+regularMiddle11 x y := by
  have hi10 : Continuous (fun z => regularInner10 x y z) := regularInner10_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)
  have hi11 : Continuous (fun z => regularInner11 x y z) := regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)
  have hn : ∀ z ∈ Icc y beta, z ≠ 0 := fun z hz =>
    (fixed_geometry.2.1.trans_le (hy.trans hz.1)).ne'
  have he : ContinuousOn ell (Icc y beta) :=
    continuousOn_const.sub (continuousOn_id.log hn)
  have h := compare_primitive (f := fun z => regularInner10 x y z+regularInner11 x y z)
    (g := fun z => (1/2)/(x*y^2)*((A+ell z)/z-1/c))
    (P := fun z => (1/2)/(x*y^2)*Z z) hyb (hi10.add hi11)
    (continuousOn_const.mul (((continuousOn_const.add he).div continuousOn_id hn).sub continuousOn_const))
    (fun z hz => (Z_derivative (hn z hz)).const_mul _) (fun z hz =>
      inner_lower hx hy (hy.trans hz.1) hz.2)
  rw [intervalIntegral.integral_add (hi10.intervalIntegrable y beta) (hi11.intervalIntegrable y beta)] at h
  change _ ≤ regularMiddle10 x y+regularMiddle11 x y at h
  convert h using 1
  simp only [Z,ell,sub_self]
  ring

theorem outer_lower {x : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) :
    (1/2)/x*(F beta-F x) ≤ regularOuter10 x+regularOuter11 x := by
  have hi10 : Continuous (fun y => regularMiddle10 x y) := regularMiddle10_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hi11 : Continuous (fun y => regularMiddle11 x y) := regularMiddle11_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hn : ∀ y ∈ Icc x beta, y ≠ 0 := fun y hy =>
    (fixed_geometry.2.1.trans_le (hx.trans hy.1)).ne'
  have he : ContinuousOn ell (Icc x beta) := continuousOn_const.sub (continuousOn_id.log hn)
  have hg : ContinuousOn (fun y => (1/2)/x*((A*ell y+ell y^2/2-(beta-y)/c)/y^2)) (Icc x beta) :=
    continuousOn_const.mul ((((continuousOn_const.mul he).add ((he.pow 2).div_const 2)).sub
      ((continuousOn_const.sub continuousOn_id).div_const c)).div (continuousOn_id.pow 2)
        (fun y hy => pow_ne_zero 2 (hn y hy)))
  have h := compare_primitive (f := fun y => regularMiddle10 x y+regularMiddle11 x y) hxb (hi10.add hi11) hg
    (fun y hy => (F_derivative (hn y hy)).const_mul ((1/2)/x))
    (fun y hy => middle_lower hx (hx.trans hy.1) hy.2)
  rw [intervalIntegral.integral_add (hi10.intervalIntegrable x beta) (hi11.intervalIntegrable x beta)] at h
  change _ ≤ regularOuter10 x+regularOuter11 x at h
  convert h using 1; ring

def exactMass (L : ℝ) : ℝ :=
  (1/(2*alpha)+1/(2*c))*L^2+
    ((A-2)/alpha+(A-1+beta/c)/beta)*L+
    (3-2*A-beta/c)*(1/alpha-1/beta)

theorem complete_real_lower : 4*exactMass tailLog ≤ 8*I10+8*I11 := by
  have hn : ∀ x ∈ Icc alpha beta, x ≠ 0 := fun x hx =>
    (fixed_geometry.2.1.trans_le hx.1).ne'
  have he : ContinuousOn ell (Icc alpha beta) := continuousOn_const.sub (continuousOn_id.log hn)
  have hf : ContinuousOn F (Icc alpha beta) := by
    exact (((((he.pow 2).neg.div_const 2).add (continuousOn_const.mul he)).add
      continuousOn_const).div continuousOn_id hn).add ((continuousOn_id.log hn).div_const c)
  have hg : ContinuousOn (fun x => (1/2)*((F beta-F x)/x)) (Icc alpha beta) :=
    continuousOn_const.mul ((continuousOn_const.sub hf).div continuousOn_id hn)
  have h := compare_primitive (f := fun x => regularOuter10 x+regularOuter11 x) fixed_geometry.2.2.1
    (regularOuter10_continuous.add regularOuter11_continuous) hg
    (fun x hx => (H_derivative (hn x hx)).const_mul (1/2)) (fun x hx => by
      convert outer_lower hx.1 hx.2 using 1; ring)
  rw [intervalIntegral.integral_add
    (regularOuter10_continuous.intervalIntegrable alpha beta)
    (regularOuter11_continuous.intervalIntegrable alpha beta),← I10_eq_regular,← I11_eq_regular] at h
  have heq : H beta-H alpha = exactMass tailLog := by
    dsimp [H,F,ell,exactMass,tailLog]
    ring
  have hh : (1/2)*H beta-(1/2)*H alpha = (1/2)*exactMass tailLog := by rw [← heq]; ring
  rw [hh] at h
  linarith

/-- Signed endpoint payment keeps both original log endpoints. -/
def rationalLower : ℝ := 4*((1/(2*alpha)+1/(2*c))*FourLogAffine.l^2+
    ((A-2)/alpha+(A-1+beta/c)/beta)*FourLogAffine.u+
    (3-2*A-beta/c)*(1/alpha-1/beta))

theorem actual_four_lower : rationalLower ≤ 8*I10+8*I11 := by
  obtain ⟨hl0,hl,_,_,_⟩ := FourLogAffine.fixed_log_bounds
  have hu := FourLogAffine.fixed_log_bounds.2.2.1
  have hp := pow_le_pow_left₀ hl0.le hl 2
  have hpos : 0 ≤ 1/(2*alpha)+1/(2*c) := by
    have ha := fixed_geometry.2.1
    have hc := c_pos
    positivity
  have hneg : (A-2)/alpha+(A-1+beta/c)/beta ≤ 0 := by
    norm_num [A,c,SharpLogRecurrence.lowerLog,alpha,beta,lam,
      truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]
  have h1 := mul_le_mul_of_nonneg_left hp hpos
  have h2 := mul_le_mul_of_nonpos_left hu hneg
  apply le_trans _ complete_real_lower
  dsimp [rationalLower,exactMass]
  linarith
end FourLower

/-- Complete original L-envelope FTC, without endpoint-log payment. -/
def jLowerReal : ℝ :=
  16*JCubicActualMass.fullMass 1 3 SharpJBalance.s (1/3)+
  8*JCubicActualMass.fullMass (1/3) 1 SharpJBalance.a (1/3)+
  8*JCubicActualMass.fullMass (1-2*SharpJBalance.s) 1 SharpJBalance.b SharpJBalance.s

/-- The three original labels and multiplicities, not an independently modeled J. -/
def actualJ : ℝ := 16*SeventhEighth.J7+8*SeventhEighth.J8+8*J9

theorem original_j_domains : actualJ =
    16*(∫ t in SeventhEighth.sigma..(1/3), log ((1-2*t)/t)/(t*(1-t)))+
    8*(∫ t in SeventhEighth.alpha..(1/3), log (2-3*t)/(t*(1-t)))+
    8*(∫ t in SharpJBalance.b..SharpJBalance.s,
      log ((1-SharpJBalance.s-t)/SharpJBalance.s)/(t*(1-t))) := by rfl

theorem complete_j_lower : jLowerReal ≤ actualJ := by
  have h7 := JCubicActualMass.seventh_mass_lower
  have h8 := JCubicActualMass.eighth_mass_lower
  have h9 := JCubicActualMass.ninth_mass_lower
  unfold jLowerReal actualJ
  linarith only [h7,h8,h9]

def jRemaining : ℝ := AnalyticTotalThreshold.jLoss-JointJLossStrength.recovery
def fourRemaining : ℝ := AnalyticTotalThreshold.fourLoss-FourActualCapRecovery.recovery

/-- The correlation and the ninth recovery are each subtracted exactly once. -/
def jCapReal : ℝ := UnroundedPayments.weightedJUpper-
  SignedTotalCorrelation.jTwo*(SignedTotalCorrelation.d2-SignedTotalCorrelation.e2)-
  JointJLossStrength.recovery-jLowerReal

/-- Explicit whole-domain bound, not just positivity of the remaining loss. -/
def jCap : ℝ := UnroundedPayments.weightedJUpper-
  JCubicRationalLower.weightedRational-JointJLossStrength.fixedRecovery

/-- The full Four tangent/crossLog payment stays inside the upper endpoint. -/
def fourCapReal : ℝ := FourActualCapRecovery.actualUpper-4*FourLower.exactMass tailLog
def fourCap : ℝ := FourActualCapRecovery.actualUpper-FourLower.rationalLower

theorem j_remaining_real_interval : 0 ≤ jRemaining ∧ jRemaining ≤ jCapReal := by
  have hlo := JointJLossStrength.actual_jLoss_lower
  have hhi := complete_j_lower
  unfold jRemaining jCapReal AnalyticTotalThreshold.jLoss actualJ at *
  constructor <;> linarith only [hlo,hhi]

theorem j_remaining_interval : 0 ≤ jRemaining ∧ jRemaining ≤ jCap := by
  have h := JCubicRationalLower.weighted_J_lower
  have hr := JointJLossStrength.fixedRecovery_le_recovery
  have hd : 0 ≤ SignedTotalCorrelation.d2-SignedTotalCorrelation.e2 := by
    unfold SignedTotalCorrelation.d2 SignedTotalCorrelation.e2
    have hl := SharpLogRecurrence.log_upper (by norm_num : (1:ℝ) ≤ 2)
    linarith only [hl]
  have hj : 0 ≤ SignedTotalCorrelation.jTwo := by
    norm_num [SignedTotalCorrelation.jTwo,SharpJBalance.ninthA,SharpJBalance.s,
      SeventhEighth.sigma,SeventhEighth.alpha]
  have hc := mul_nonneg hj hd
  refine ⟨j_remaining_real_interval.1,?_⟩
  unfold jRemaining jCap AnalyticTotalThreshold.jLoss
  linarith only [h,hr,hc]

theorem four_remaining_identity : fourRemaining =
    FourActualCapRecovery.actualUpper-(8*I10+8*I11) := by
  unfold fourRemaining AnalyticTotalThreshold.fourLoss FourActualCapRecovery.recovery
  ring

theorem four_remaining_real_interval : 0 ≤ fourRemaining ∧ fourRemaining ≤ fourCapReal := by
  have hl := FourLower.complete_real_lower
  have hu := FourActualCapRecovery.actual_four_upper
  rw [four_remaining_identity]
  unfold fourCapReal
  constructor <;> linarith only [hl,hu]

theorem four_remaining_interval : 0 ≤ fourRemaining ∧ fourRemaining ≤ fourCap := by
  have hl := FourLower.actual_four_lower
  have hu := FourActualCapRecovery.actual_four_upper
  rw [four_remaining_identity]
  unfold fourCap
  constructor <;> linarith only [hl,hu]

/-- A concrete positive lower endpoint for the actual 8 I10 + 8 I11. -/
theorem actual_four_magnitude : (587/1000:ℝ) < 8*I10+8*I11 ∧
    8*I10+8*I11 < 713/1000 := by
  have hl : (587/1000:ℝ) < FourLower.rationalLower := by
    norm_num [FourLower.rationalLower,FourLower.c,FourLower.A,FourLogAffine.l,FourLogAffine.u,
      SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,alpha,beta,lam,
      truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]
  have hu : FourActualCapRecovery.actualUpper < (713/1000:ℝ) := by
    norm_num [FourActualCapRecovery.actualUpper,FourActualCapRecovery.cap,Phase24.exactMass,
      Phase24.A,Phase24.c,FourLogAffine.w,FourLogAffine.u,
      SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,alpha,beta,lam,
      truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]
  exact ⟨hl.trans_le FourLower.actual_four_lower,FourActualCapRecovery.actual_four_upper.trans_lt hu⟩

theorem j_cap_size : jCap < (1045/10000:ℝ) := by
  unfold jCap
  rw [JCubicRationalLower.weighted_exact]
  norm_num [UnroundedPayments.weightedJUpper,UnroundedPayments.j7Upper,
    UnroundedPayments.j8Upper,UnroundedPayments.j9Upper,JointJLossStrength.fixedRecovery,
    JointJLossStrength.massPayment,SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,
    SharpJBalance.s,SharpJBalance.b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2]

theorem four_cap_size : fourCap < (1247/10000:ℝ) := by
  norm_num [fourCap,FourActualCapRecovery.actualUpper,FourActualCapRecovery.cap,Phase24.exactMass,
    Phase24.A,Phase24.c,FourLower.rationalLower,FourLower.A,FourLower.c,
    FourLogAffine.l,FourLogAffine.u,FourLogAffine.w,
    SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,alpha,beta,lam,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

/-- Original parameters lie beyond the initial Buchstab segment; no clipping at two. -/
theorem actual_four_parameter_range {x y z t : ℝ}
    (hx : alpha ≤ x) (hxb : x ≤ beta) (hy : alpha ≤ y) (hyb : y ≤ beta)
    (hz : alpha ≤ z) (ht : alpha ≤ t) (htu : t ≤ lam-z) :
    10/3 < parameter x y z t ∧ parameter x y z t ≤ 927/100 ∧
    max 2 (parameter x y z t) = parameter x y z t := by
  have h := ClassicalLossBottleneck.four_parameter_range hxb hy hyb htu
  exact ⟨h.1,FourActualCapRecovery.parameter_upper hx hy hz ht,h.2⟩

def recoveredCoefficient : ℝ := AnalyticTotalThreshold.coefficient+
  (JointJLossStrength.recovery+FourActualCapRecovery.recovery)/4

/-- All five other actual-error labels remain on the same mother coefficient. -/
def otherLosses : ℝ := AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+
  AnalyticTotalThreshold.sharedLoss+AnalyticTotalThreshold.fifthLoss+AnalyticTotalThreshold.sixthLoss

def residualCap : ℝ := (jCap+fourCap)/4

theorem original_mother_identity :
    JointHMotherPayment.unroundedCoefficient-recoveredCoefficient =
      (otherLosses+jRemaining+fourRemaining)/4 := by
  have h := AnalyticTotalThreshold.actual_gap_identity
  rw [AnalyticTotalThreshold.signed_loss_identity] at h
  unfold recoveredCoefficient otherLosses jRemaining fourRemaining
  linarith only [h]

/-- Unconditional interval for the two remaining actual errors, with all other errors labeled. -/
theorem original_mother_residual_interval :
    0 ≤ JointHMotherPayment.unroundedCoefficient-recoveredCoefficient-otherLosses/4 ∧
    JointHMotherPayment.unroundedCoefficient-recoveredCoefficient-otherLosses/4 ≤ residualCap := by
  have he := original_mother_identity
  have hj := j_remaining_interval
  have hf := four_remaining_interval
  unfold residualCap
  constructor <;> linarith only [he,hj.1,hj.2,hf.1,hf.2]

theorem residual_cap_size : residualCap < (573/10000:ℝ) := by
  have hj := j_cap_size
  have hf := four_cap_size
  unfold residualCap
  linarith only [hj,hf]

/-- A real error upper bound, not an additional hypothesis for a threshold theorem. -/
theorem actual_residual_magnitude :
    0 ≤ (jRemaining+fourRemaining)/4 ∧ (jRemaining+fourRemaining)/4 < 573/10000 := by
  have hj := j_remaining_interval
  have hf := four_remaining_interval
  have hc := residual_cap_size
  unfold residualCap at hc
  constructor <;> linarith only [hj.1,hj.2,hf.1,hf.2,hc]

end
end Wu2008DoubleSieve.JFourRemainingMagnitude
