import ClassicalLossBottleneck

namespace Wu2008DoubleSieve.FourActualCapRecovery
open Real Set MeasureTheory FourRoughClosedMass ClassicalLogFourBounds
open Phase24 (c A Z F H exactMass compare_primitive Z_derivative F_derivative H_derivative ell_derivative)
open FourLogAffine (ell)
open LiLiuPrereqBuchstab SecondFunctionalFourSevenths
open scoped Interval
noncomputable section

def cap : ℝ := 4/7-(5/252)/(927/100)

theorem cap_pos : 0 < cap := by norm_num [cap]

/-- Actual Buchstab recurrence beyond three retains its endpoint deficit. -/
theorem buchstab_endpoint_deficit {s : ℝ} (hs : 3 ≤ s) :
    s * buchstab s ≤ (4/7)*s-5/252 := by
  have he := buchstab_increment (u := s) (v := 3) (by norm_num) hs
  have hi := intervalIntegral.integral_mono_on (μ := volume)
    (show (3:ℝ)-1 ≤ s-1 by linarith)
    (continuous_buchstab.intervalIntegrable (3-1) (s-1))
    (intervalIntegrable_const (c := (4/7:ℝ)))
    (fun t ht => buchstab_le_four_sevenths (by linarith [ht.1]))
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hi
  have h3 := buchstab_log_segment (u := 3) (by norm_num) le_rfl
  norm_num only [show (3:ℝ)-1=2 by norm_num] at h3
  have hl := SharpLogRecurrence.log_two_bounds.2
  rw [h3] at he
  linarith

/-- No new integration cut: this covers the entire original actual range. -/
theorem buchstab_actual_cap {s : ℝ} (hs : 3 ≤ s) (hu : s ≤ 927/100) :
    buchstab s ≤ cap := by
  have h := buchstab_endpoint_deficit hs
  have hm := mul_le_mul_of_nonneg_left hu (by norm_num : (0:ℝ) ≤ (5/252)/(927/100))
  apply (mul_le_mul_iff_right₀ (show 0 < s by linarith)).mp
  dsimp [cap]
  nlinarith

/-- The original denominator and ordering bound the actual delay parameter. -/
theorem parameter_upper {x y z t : ℝ} (hx : alpha ≤ x) (hy : alpha ≤ y)
    (hz : alpha ≤ z) (ht : alpha ≤ t) : parameter x y z t ≤ 927/100 := by
  have hy0 := fixed_geometry.2.1.trans_le hy
  unfold parameter
  apply (div_le_iff₀ hy0).2
  norm_num [alpha,truncatedSixthLowerAlpha] at hx hy hz ht
  linarith

/-- Improved cap on the literal original regular kernel; no model substitution. -/
theorem regular_reciprocal_sq {x y z t : ℝ}
    (hx : alpha ≤ x) (hxb : x ≤ beta) (hy : alpha ≤ y) (hyb : y ≤ beta)
    (hz : alpha ≤ z) (ht : alpha ≤ t) (htu : t ≤ lam-z) :
    regularKernel x y z t ≤ cap/(x*y^2*z*t) := by
  have hx0 := fixed_geometry.2.1.trans_le hx
  have hy0 := fixed_geometry.2.1.trans_le hy
  have hz0 := fixed_geometry.2.1.trans_le hz
  have ht0 := fixed_geometry.2.1.trans_le ht
  have hr := ClassicalLossBottleneck.four_parameter_range hxb hy hyb htu
  have hb := buchstab_actual_cap (by linarith [hr.1]) (parameter_upper hx hy hz ht)
  simp only [regularKernel,clip,max_eq_right hx,max_eq_right hy,
    max_eq_right hz,max_eq_right ht,hr.2]
  exact div_le_div_of_nonneg_right hb (by positivity)

theorem inner_upper {x y z : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) (hy : alpha ≤ y) (hyb : y ≤ beta)
    (hz : alpha ≤ z) (hzb : z ≤ beta) :
    regularInner10 x y z+regularInner11 x y z ≤
      cap/(x*y^2)*((A+ell z)/z-1/c) := by
  have hk := cap_pos
  have hx0 := fixed_geometry.2.1.trans_le hx
  have hy0 := fixed_geometry.2.1.trans_le hy
  have hz0 := fixed_geometry.2.1.trans_le hz
  have ho : z ≤ lam-z := by linarith [fixed_geometry.2.2.2.2.2.2.1]
  rw [Phase24.inner_join]
  have h := integral_le_log_tail (C := cap/(x*y^2*z))
    (regularKernel_continuous.comp (f := fun t : ℝ => (x,y,z,t)) (by fun_prop))
    hz0 ho 0 (fun t ht => by
      have hh := regular_reciprocal_sq hx hxb hy hyb hz (hz.trans ht.1) ht.2
      convert hh using 1 <;> first | rfl | ring)
  norm_num only [Nat.cast_zero,zero_add,pow_one,div_one] at h
  have hl := Phase24.moving_log_tangent hz hzb
  have hw := FourLogAffine.fixed_log_bounds.2.2.2.2
  have htail : log (lam-z)-log z ≤ A+ell z-z/c := by
    dsimp [A,ell,c,crossLog] at *
    rw [sub_div] at hl
    linarith
  have hm := mul_le_mul_of_nonneg_left htail
    (show 0 ≤ cap/(x*y^2*z) by positivity)
  refine h.trans (hm.trans_eq ?_)
  field_simp


theorem middle_upper {x y : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) (hy : alpha ≤ y) (hyb : y ≤ beta) :
    regularMiddle10 x y+regularMiddle11 x y ≤
      cap/x*((A*ell y+ell y^2/2-(beta-y)/c)/y^2) := by
  have hi10 : Continuous (fun z => regularInner10 x y z) := regularInner10_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)
  have hi11 : Continuous (fun z => regularInner11 x y z) := regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)
  have hn : ∀ z ∈ Icc y beta, z ≠ 0 := fun z hz =>
    (fixed_geometry.2.1.trans_le (hy.trans hz.1)).ne'
  have he : ContinuousOn ell (Icc y beta) :=
    continuousOn_const.sub (continuousOn_id.log hn)
  have h := compare_primitive (f := fun z => regularInner10 x y z+regularInner11 x y z)
    (g := fun z => cap/(x*y^2)*((A+ell z)/z-1/c))
    (P := fun z => cap/(x*y^2)*Z z) hyb (hi10.add hi11)
    (continuousOn_const.mul (((continuousOn_const.add he).div continuousOn_id hn).sub continuousOn_const))
    (fun z hz => (Z_derivative (hn z hz)).const_mul _) (fun z hz =>
      inner_upper hx hxb hy hyb (hy.trans hz.1) hz.2)
  rw [intervalIntegral.integral_add (hi10.intervalIntegrable y beta) (hi11.intervalIntegrable y beta)] at h
  change regularMiddle10 x y+regularMiddle11 x y ≤ _ at h
  convert h using 1
  simp only [Z,ell,sub_self]
  ring

theorem outer_upper {x : ℝ} (hx : alpha ≤ x) (hxb : x ≤ beta) :
    regularOuter10 x+regularOuter11 x ≤ cap/x*(Phase24.F beta-Phase24.F x) := by
  have hi10 : Continuous (fun y => regularMiddle10 x y) := regularMiddle10_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hi11 : Continuous (fun y => regularMiddle11 x y) := regularMiddle11_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hn : ∀ y ∈ Icc x beta, y ≠ 0 := fun y hy =>
    (fixed_geometry.2.1.trans_le (hx.trans hy.1)).ne'
  have he : ContinuousOn ell (Icc x beta) := continuousOn_const.sub (continuousOn_id.log hn)
  have hg : ContinuousOn (fun y => cap/x*((A*ell y+ell y^2/2-(beta-y)/c)/y^2)) (Icc x beta) :=
    continuousOn_const.mul ((((continuousOn_const.mul he).add ((he.pow 2).div_const 2)).sub
      ((continuousOn_const.sub continuousOn_id).div_const c)).div (continuousOn_id.pow 2)
        (fun y hy => pow_ne_zero 2 (hn y hy)))
  have h := compare_primitive (f := fun y => regularMiddle10 x y+regularMiddle11 x y) hxb (hi10.add hi11) hg
    (fun y hy => (F_derivative (hn y hy)).const_mul (cap/x))
    (fun y hy => middle_upper hx hxb (hx.trans hy.1) hy.2)
  rw [intervalIntegral.integral_add (hi10.intervalIntegrable x beta) (hi11.intervalIntegrable x beta)] at h
  change regularOuter10 x+regularOuter11 x ≤ _ at h
  convert h using 1; ring


theorem complete_real_upper : 8*I10+8*I11 ≤ (8*cap)*exactMass tailLog := by
  have hn : ∀ x ∈ Icc alpha beta, x ≠ 0 := fun x hx =>
    (fixed_geometry.2.1.trans_le hx.1).ne'
  have he : ContinuousOn ell (Icc alpha beta) := continuousOn_const.sub (continuousOn_id.log hn)
  have hf : ContinuousOn Phase24.F (Icc alpha beta) := by
    exact (((((he.pow 2).neg.div_const 2).add (continuousOn_const.mul he)).add
      continuousOn_const).div continuousOn_id hn).add ((continuousOn_id.log hn).div_const c)
  have hg : ContinuousOn (fun x => cap*((Phase24.F beta-Phase24.F x)/x)) (Icc alpha beta) :=
    continuousOn_const.mul ((continuousOn_const.sub hf).div continuousOn_id hn)
  have h := compare_primitive (f := fun x => regularOuter10 x+regularOuter11 x) fixed_geometry.2.2.1
    (regularOuter10_continuous.add regularOuter11_continuous) hg
    (fun x hx => (H_derivative (hn x hx)).const_mul cap) (fun x hx => by
      convert outer_upper hx.1 hx.2 using 1; ring)
  rw [intervalIntegral.integral_add
    (regularOuter10_continuous.intervalIntegrable alpha beta)
    (regularOuter11_continuous.intervalIntegrable alpha beta),← I10_eq_regular,← I11_eq_regular] at h
  have heq : H beta-H alpha = exactMass tailLog := by
    dsimp [H,Phase24.F,ell,exactMass,tailLog]
    ring
  have hh : cap*H beta-cap*H alpha = cap*exactMass tailLog := by rw [← heq]; ring
  rw [hh] at h
  linarith

/-- One correlated quadratic payment, rather than separate positive/negative payments. -/
def actualUpper : ℝ := 8*cap*exactMass FourLogAffine.u

theorem correlated_mass_upper : exactMass tailLog ≤ exactMass FourLogAffine.u := by
  obtain ⟨hl0,hl,hu,_,_⟩ := FourLogAffine.fixed_log_bounds
  have hp : 0 ≤ 1/(2*alpha)+1/(2*c) := by
    have ha := fixed_geometry.2.1
    have hc := Phase24.c_pos
    positivity
  have hd : 0 ≤ 2*(1/(2*alpha)+1/(2*c))*FourLogAffine.l+
      (A-2)/alpha+(A-1+beta/c)/beta := by
    norm_num [A,c,FourLogAffine.l,FourLogAffine.w,SharpLogRecurrence.lowerLog,
      SharpLogRecurrence.upperLog,alpha,beta,lam,truncatedSixthLowerAlpha,
      truncatedSixthLowerBeta,truncatedSixthLowerLambda]
  have hsum : 2*FourLogAffine.l ≤ FourLogAffine.u+tailLog := by linarith
  have hprod := mul_le_mul_of_nonneg_left hsum hp
  have hnon : 0 ≤ (1/(2*alpha)+1/(2*c))*(FourLogAffine.u+tailLog)+
      ((A-2)/alpha+(A-1+beta/c)/beta) := by linarith
  have h := mul_nonneg (sub_nonneg.mpr hu) hnon
  unfold exactMass
  nlinarith only [h]

/-- A stronger upper bound on 8 I10 + 8 I11 itself. -/
theorem actual_four_upper : 8*I10+8*I11 ≤ actualUpper := by
  exact complete_real_upper.trans (mul_le_mul_of_nonneg_left correlated_mass_upper
    (mul_nonneg (by norm_num) cap_pos.le))

def recovery : ℝ := Phase24.newFour-actualUpper

/-- The entire fixed rational recovery is retained, not a chosen small epsilon. -/
theorem recovery_exact : recovery =
    37716897485533191145002630415643113/1895520972114527291354873739828960000 := by
  norm_num [recovery,Phase24.newFour,actualUpper,exactMass,cap,A,c,
    FourLogAffine.l,FourLogAffine.u,FourLogAffine.w,SharpLogRecurrence.lowerLog,
    SharpLogRecurrence.upperLog,alpha,beta,lam,truncatedSixthLowerAlpha,
    truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem recovery_size : (1/100:ℝ) < recovery := by rw [recovery_exact]; norm_num

/-- This lower bound is for the actual fourLoss, with both multiplicities unchanged. -/
theorem actual_fourLoss_lower : recovery ≤ AnalyticTotalThreshold.fourLoss := by
  have h := actual_four_upper
  unfold recovery AnalyticTotalThreshold.fourLoss
  linarith only [h]

def recoveredCoefficient : ℝ := AnalyticTotalThreshold.coefficient+recovery/4

/-- Same seven-error identity, spending the Four recovery exactly once. -/
theorem remaining_gap_identity :
    JointHMotherPayment.unroundedCoefficient-recoveredCoefficient =
      (AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+
       AnalyticTotalThreshold.jLoss+AnalyticTotalThreshold.sharedLoss+
       AnalyticTotalThreshold.fifthLoss+AnalyticTotalThreshold.sixthLoss+
       (AnalyticTotalThreshold.fourLoss-recovery))/4 := by
  have h := AnalyticTotalThreshold.actual_gap_identity
  rw [AnalyticTotalThreshold.signed_loss_identity] at h
  unfold recoveredCoefficient
  linarith only [h]

theorem recoveredCoefficient_le_actual :
    recoveredCoefficient ≤ JointHMotherPayment.unroundedCoefficient := by
  have hg := remaining_gap_identity
  have hs := AnalyticTotalThreshold.signed_losses_nonnegative
  have hl := AnalyticTotalThreshold.losses_nonnegative
  have hf := actual_fourLoss_lower
  linarith only [hg,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hl.2.1,hl.2.2.1,hf]

end
end Wu2008DoubleSieve.FourActualCapRecovery
