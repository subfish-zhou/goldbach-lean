import JFourRemainingMagnitude

namespace Wu2008DoubleSieve.FourTrueLowerTight
open Real Set MeasureTheory FourRoughClosedMass ClassicalLogFourBounds
open LiLiuPrereqBuchstab SecondFunctionalFourSevenths
open JFourRemainingMagnitude.FourLower (c A Z F H exactMass c_pos moving_log_lower
  ell_derivative Z_derivative F_derivative H_derivative compare_primitive)
open FourLogAffine (ell)
open scoped Interval
noncomputable section

/-- The original lower logarithm payment at the natural recurrence endpoint. -/
def lower : ℝ := (3/2+SharpLogRecurrence.lowerLog 2)/4

theorem lower_exact : lower = 355/648 := by norm_num [lower,SharpLogRecurrence.lowerLog]
theorem lower_pos : 0 < lower := by rw [lower_exact]; norm_num

/-- The actual recurrence anchored at three, on its complete next unit interval. -/
theorem buchstab_seed_lower {s : ℝ} (hs : 3 ≤ s) (hu : s ≤ 4) :
    lower ≤ buchstab s := by
  have he := buchstab_increment (u := s) (v := 3) (by norm_num) hs
  have hi := intervalIntegral.integral_mono_on (μ := volume)
    (show (3:ℝ)-1 ≤ s-1 by linarith)
    (intervalIntegrable_const (c := (1/2:ℝ)))
    (continuous_buchstab.intervalIntegrable (3-1) (s-1))
    (fun t ht => one_half_le_buchstab (by linarith [ht.1]))
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hi
  have h3 := buchstab_log_segment (u := 3) (by norm_num) le_rfl
  norm_num only [show (3:ℝ)-1=2 by norm_num] at h3
  rw [h3] at he
  have hl := SharpLogRecurrence.log_two_bounds.1
  rw [lower_exact]
  apply (mul_le_mul_iff_left₀ (show 0 < s by linarith)).mp
  nlinarith

/-- Constant lower barriers propagate by the true positive delay integral. -/
theorem buchstab_lower_step {v : ℝ} (hv : 4 ≤ v)
    (hh : ∀ t : ℝ, 3 ≤ t → t ≤ v → lower ≤ buchstab t)
    {s : ℝ} (hvs : v ≤ s) (hs : s ≤ v+1) : lower ≤ buchstab s := by
  have hi := intervalIntegral.integral_mono_on (μ := volume)
    (show v-1 ≤ s-1 by linarith)
    (intervalIntegrable_const (c := lower))
    (continuous_buchstab.intervalIntegrable (v-1) (s-1))
    (fun t ht => hh t (by linarith [ht.1]) (by linarith [ht.2]))
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hi
  have he := buchstab_increment (by linarith : 2 ≤ v) hvs
  have hb := mul_le_mul_of_nonneg_left (hh v (by linarith) le_rfl)
    (show 0 ≤ v by linarith)
  apply (mul_le_mul_iff_left₀ (show 0 < s by linarith)).mp
  nlinarith only [hi,he,hb]

theorem buchstab_lower_prefix (n : ℕ) :
    ∀ s : ℝ, 3 ≤ s → s ≤ (n:ℝ)+4 → lower ≤ buchstab s := by
  induction n with
  | zero => simpa using fun s hs hu => buchstab_seed_lower (s := s) hs hu
  | succ n ih =>
    intro s hs hu
    by_cases hn : s ≤ (n:ℝ)+4
    · exact ih s hs hn
    · apply buchstab_lower_step (v := (n:ℝ)+4)
        (by linarith [Nat.cast_nonneg (α := ℝ) n]) ih (le_of_not_ge hn)
      push_cast at hu
      linarith

/-- An unconditional true Buchstab lower bound, not a normalized sieve function. -/
theorem buchstab_true_lower {s : ℝ} (hs : 3 ≤ s) : lower ≤ buchstab s := by
  obtain ⟨n,hn⟩ := exists_nat_gt s
  exact buchstab_lower_prefix n s hs (by linarith)

/-- Literal original kernel, including the squared second coordinate. -/
theorem regular_lower {x y z t : ℝ}
    (hx : alpha ≤ x) (hxb : x ≤ beta) (hy : alpha ≤ y) (hyb : y ≤ beta)
    (hz : alpha ≤ z) (ht : alpha ≤ t) (htu : t ≤ lam-z) :
    lower/(x*y^2*z*t) ≤ regularKernel x y z t := by
  have hx0 := fixed_geometry.2.1.trans_le hx
  have hy0 := fixed_geometry.2.1.trans_le hy
  have hz0 := fixed_geometry.2.1.trans_le hz
  have ht0 := fixed_geometry.2.1.trans_le ht
  have hr := ClassicalLossBottleneck.four_parameter_range hxb hy hyb htu
  have hb := buchstab_true_lower (by linarith [hr.1] : 3 ≤ parameter x y z t)
  simp only [regularKernel,clip,max_eq_right hx,max_eq_right hy,
    max_eq_right hz,max_eq_right ht,hr.2]
  exact div_le_div_of_nonneg_right hb (by positivity)

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
  have hw := SharpLogRecurrence.log_lower (t := (lam-alpha)/beta)
    (by norm_num [lam,alpha,beta,truncatedSixthLowerLambda,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  rw [log_div (show lam-alpha ≠ 0 from Phase24.c_pos.ne') hb0.ne'] at hw
  have htail : A+ell z-z/c ≤ log (lam-z)-log z := by
    dsimp [A,ell] at *
    rw [sub_div] at hl
    linarith
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
    lower/x*(JFourRemainingMagnitude.FourLower.F beta-JFourRemainingMagnitude.FourLower.F x) ≤ regularOuter10 x+regularOuter11 x := by
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
  have hf : ContinuousOn JFourRemainingMagnitude.FourLower.F (Icc alpha beta) := by
    exact (((((he.pow 2).neg.div_const 2).add (continuousOn_const.mul he)).add
      continuousOn_const).div continuousOn_id hn).add ((continuousOn_id.log hn).div_const c)
  have hg : ContinuousOn (fun x => lower*((JFourRemainingMagnitude.FourLower.F beta-JFourRemainingMagnitude.FourLower.F x)/x)) (Icc alpha beta) :=
    continuousOn_const.mul ((continuousOn_const.sub hf).div continuousOn_id hn)
  have h := compare_primitive (f := fun x => regularOuter10 x+regularOuter11 x) fixed_geometry.2.2.1
    (regularOuter10_continuous.add regularOuter11_continuous) hg
    (fun x hx => (H_derivative (hn x hx)).const_mul lower) (fun x hx => by
      convert outer_lower hx.1 hx.2 using 1; ring)
  rw [intervalIntegral.integral_add
    (regularOuter10_continuous.intervalIntegrable alpha beta)
    (regularOuter11_continuous.intervalIntegrable alpha beta),← I10_eq_regular,← I11_eq_regular] at h
  have heq : H beta-H alpha = exactMass tailLog := by
    dsimp [H,JFourRemainingMagnitude.FourLower.F,ell,exactMass,tailLog]
    ring
  have hh : lower*H beta-lower*H alpha = lower*exactMass tailLog := by rw [← heq]; ring
  rw [hh] at h
  linarith


/-- Retain the same logarithm in both signed quadratic terms. -/
theorem correlated_mass_lower : exactMass FourLogAffine.l ≤ exactMass tailLog := by
  obtain ⟨_,hl,_,_,_⟩ := FourLogAffine.fixed_log_bounds
  have hp : 0 ≤ 1/(2*alpha)+1/(2*c) := by
    have ha := fixed_geometry.2.1
    have hc := c_pos
    positivity
  have hd : 0 ≤ 2*(1/(2*alpha)+1/(2*c))*FourLogAffine.l+
      (A-2)/alpha+(A-1+beta/c)/beta := by
    norm_num [A,c,FourLogAffine.l,SharpLogRecurrence.lowerLog,
      alpha,beta,lam,truncatedSixthLowerAlpha,
      truncatedSixthLowerBeta,truncatedSixthLowerLambda]
  have hm := mul_le_mul_of_nonneg_left
    (show 2*FourLogAffine.l ≤ tailLog+FourLogAffine.l by linarith) hp
  have hnon : 0 ≤ (1/(2*alpha)+1/(2*c))*(tailLog+FourLogAffine.l)+
      ((A-2)/alpha+(A-1+beta/c)/beta) := by linarith
  have h := mul_nonneg (sub_nonneg.mpr hl) hnon
  unfold exactMass
  nlinarith only [h]

/-- Full rational lower endpoint, with no separately rounded signed terms. -/
def actualLower : ℝ := 8*lower*exactMass FourLogAffine.l

theorem actual_four_lower : actualLower ≤ 8*I10+8*I11 := by
  exact (mul_le_mul_of_nonneg_left correlated_mass_lower
    (mul_nonneg (by norm_num) lower_pos.le)).trans complete_real_lower

theorem actual_lower_exact : actualLower =
    1164192833831812693571703848634850838798981/
    1773766889042401299312875202384227045469120 := by
  norm_num [actualLower,lower,exactMass,A,c,FourLogAffine.l,SharpLogRecurrence.lowerLog,
    alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

/-- This is upper minus an actual lower bound, not upper minus upper. -/
def remainingCap : ℝ := FourActualCapRecovery.actualUpper-actualLower

theorem four_remaining_interval :
    0 ≤ JFourRemainingMagnitude.fourRemaining ∧
    JFourRemainingMagnitude.fourRemaining ≤ remainingCap := by
  have hl := actual_four_lower
  have hu := FourActualCapRecovery.actual_four_upper
  rw [JFourRemainingMagnitude.four_remaining_identity]
  unfold remainingCap
  constructor <;> linarith only [hl,hu]

theorem remaining_cap_size : remainingCap < (558/10000:ℝ) := by
  rw [remainingCap,actual_lower_exact]
  norm_num [FourActualCapRecovery.actualUpper,FourActualCapRecovery.cap,Phase24.exactMass,
    Phase24.A,Phase24.c,FourLogAffine.w,FourLogAffine.u,
    SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,alpha,beta,lam,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

/-- The original fourfold integrals and multiplicities have a tighter actual range. -/
theorem actual_four_magnitude : (6563/10000:ℝ) < 8*I10+8*I11 ∧
    8*I10+8*I11 < 713/1000 := by
  have hl : (6563/10000:ℝ) < actualLower := by rw [actual_lower_exact]; norm_num
  exact ⟨hl.trans_le actual_four_lower,JFourRemainingMagnitude.actual_four_magnitude.2⟩

theorem actual_remaining_magnitude :
    0 ≤ JFourRemainingMagnitude.fourRemaining ∧
    JFourRemainingMagnitude.fourRemaining < 558/10000 :=
  ⟨four_remaining_interval.1,four_remaining_interval.2.trans_lt remaining_cap_size⟩

/-- More than half of the previous unspent Four uncertainty is eliminated. -/
theorem cap_reduction : remainingCap < JFourRemainingMagnitude.fourCap/2 := by
  rw [remainingCap,actual_lower_exact]
  norm_num [JFourRemainingMagnitude.fourCap,FourActualCapRecovery.actualUpper,
    FourActualCapRecovery.cap,Phase24.exactMass,Phase24.A,Phase24.c,
    JFourRemainingMagnitude.FourLower.rationalLower,A,c,
    FourLogAffine.l,FourLogAffine.u,FourLogAffine.w,
    SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,alpha,beta,lam,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

/-- The contribution to the mother's uncertainty retains the original division by four. -/
theorem mother_four_uncertainty :
    0 ≤ JFourRemainingMagnitude.fourRemaining/4 ∧
    JFourRemainingMagnitude.fourRemaining/4 < 279/20000 := by
  have h := actual_remaining_magnitude
  constructor <;> linarith only [h.1,h.2]

end
end Wu2008DoubleSieve.FourTrueLowerTight
