import GlobalSignedActualComparison

namespace Wu2008DoubleSieve.BuchstabSeedTightLower
open Real Set MeasureTheory FourRoughClosedMass ClassicalLogFourBounds
open LiLiuPrereqBuchstab SecondFunctionalFourSevenths
open JFourRemainingMagnitude.FourLower (c A Z F H exactMass c_pos moving_log_lower
  ell_derivative Z_derivative F_derivative H_derivative compare_primitive)
open FourLogAffine (ell)
open scoped Interval
noncomputable section

def lower : ℝ := 14/25
theorem lower_pos : 0 < lower := by norm_num [lower]

/-- The original L, pulled back along the full natural delay interval. -/
def seedKernel (t : ℝ) : ℝ := 11/(3*t)-8/t^2+8/t^3-16/(3*t^4)
def seedPrimitive (t : ℝ) : ℝ := 11/3*log t+8/t-4/t^2+16/(9*t^3)

theorem seed_derivative {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt seedPrimitive (seedKernel t) t := by
  have h := (((hasDerivAt_log ht).const_mul (11/3:ℝ)).add
    ((hasDerivAt_const t (8:ℝ)).div (hasDerivAt_id t) ht)).sub
    ((hasDerivAt_const t (4:ℝ)).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht))
  have h' := h.add ((hasDerivAt_const t (16:ℝ)).div (((hasDerivAt_id t).pow 3).const_mul 9) (mul_ne_zero (by norm_num) (pow_ne_zero 3 ht)))
  convert h' using 1 <;> first | rfl | (dsimp [seedKernel]; field_simp; ring)

theorem seed_kernel_lower {t : ℝ} (ht : 2 ≤ t) (hu : t ≤ 3) :
    seedKernel t ≤ buchstab t := by
  rw [buchstab_log_segment ht hu]
  have hl := SharpLogRecurrence.log_lower (t := t-1) (by linarith)
  have hn : t ≠ 0 := by linarith
  have he : seedKernel t = (1+SharpLogRecurrence.lowerLog (t-1))/t := by
    unfold seedKernel SharpLogRecurrence.lowerLog
    simp only [sub_add_cancel]
    field_simp
    ring
  rw [he]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- Exact algebraic positivity on the whole interval; the square is not an interval cut. -/
def seedCertificate (t : ℝ) : ℝ :=
  11776*(3-t)^7+46720*(t-2)*(3-t)^6+42628*(t-2)^2*(3-t)^5+
  4316*(t-2)^2*(3-t)^3*((t-2)-(3-t))^2+
  23256*(t-2)^4*(3-t)^3+137520*(t-2)^5*(3-t)^2+
  113850*(t-2)^6*(3-t)+23400*(t-2)^7

theorem seed_payment {t : ℝ} (ht : 2 ≤ t) (hu : t ≤ 3) :
    lower*(t+1) ≤ 1+log 2+seedPrimitive t-seedPrimitive 2 := by
  have ht0 : t ≠ 0 := by linarith
  have hp0 : t+2 ≠ 0 := by linarith
  have hcert : 0 ≤ seedCertificate t := by
    have h0 : 0 ≤ t-2 := by linarith
    have h1 : 0 ≤ 3-t := by linarith
    unfold seedCertificate
    positivity
  have he : 11/3*SharpLogRecurrence.lowerLog (t/2)+8/t-4/t^2+16/(9*t^3)-124/81-
      lower*(t+1) = seedCertificate t/(2025*t^3*(t+2)^3) := by
    unfold SharpLogRecurrence.lowerLog lower seedCertificate
    field_simp
    ring
  have hn : 0 ≤ 11/3*SharpLogRecurrence.lowerLog (t/2)+8/t-4/t^2+16/(9*t^3)-124/81-
      lower*(t+1) := by
    rw [he]
    exact div_nonneg hcert (by positivity)
  have hl := SharpLogRecurrence.log_lower (t := t/2) (by linarith)
  have h2 := SharpLogRecurrence.log_two_bounds.1
  rw [log_div ht0 (by norm_num : (2:ℝ) ≠ 0)] at hl
  norm_num [SharpLogRecurrence.lowerLog] at h2
  unfold seedPrimitive
  norm_num
  linarith only [hn,hl,h2]

/-- Full FTC on [2,s-1], with the genuine explicit Buchstab segment retained. -/
theorem buchstab_seed_lower {s : ℝ} (hs : 3 ≤ s) (hu : s ≤ 4) :
    lower ≤ buchstab s := by
  have hn : ∀ t ∈ Icc (2:ℝ) (s-1), t ≠ 0 := fun t ht => by linarith [ht.1]
  have hc : ContinuousOn seedKernel (Icc (2:ℝ) (s-1)) := by
    unfold seedKernel
    exact (((continuousOn_const.div (continuousOn_const.mul continuousOn_id)
      (fun t ht => mul_ne_zero (by norm_num) (hn t ht))).sub
      (continuousOn_const.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (hn t ht)))).add
      (continuousOn_const.div (continuousOn_id.pow 3) (fun t ht => pow_ne_zero 3 (hn t ht)))).sub
      (continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 4))
        (fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 4 (hn t ht))))
  have hi := compare_primitive (f := buchstab) (g := seedKernel) (P := seedPrimitive)
    (show (2:ℝ) ≤ s-1 by linarith) continuous_buchstab hc
    (fun t ht => seed_derivative (hn t ht))
    (fun t ht => seed_kernel_lower ht.1 (by linarith [ht.2]))
  have he := buchstab_increment (u := s) (v := 3) (by norm_num) hs
  have h3 := buchstab_log_segment (u := 3) (by norm_num) le_rfl
  norm_num at h3 he
  rw [h3] at he
  have hp := seed_payment (t := s-1) (by linarith) (by linarith)
  apply (mul_le_mul_iff_left₀ (show 0 < s by linarith)).mp
  nlinarith only [hi,he,hp]

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


theorem actual_lower_exact : actualLower = 114779575166516744436646858316112054529477/171080911365972347541751080476873750527500 := by
  norm_num [actualLower,lower,exactMass,A,c,FourLogAffine.l,SharpLogRecurrence.lowerLog,
    alpha,beta,lam,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

def remainingCap : ℝ := FourActualCapRecovery.actualUpper-actualLower

theorem four_remaining_interval :
    0 ≤ JFourRemainingMagnitude.fourRemaining ∧
    JFourRemainingMagnitude.fourRemaining ≤ remainingCap := by
  have hl := actual_four_lower
  have hu := FourActualCapRecovery.actual_four_upper
  rw [JFourRemainingMagnitude.four_remaining_identity]
  unfold remainingCap
  constructor <;> linarith only [hl,hu]

theorem remaining_cap_exact : remainingCap = 883853310815175667225489640323346764026548759948050805977/21443590026536463186410713514307830090229693255655499424000 := by
  rw [remainingCap,actual_lower_exact]
  norm_num [FourActualCapRecovery.actualUpper,FourActualCapRecovery.cap,Phase24.exactMass,
    Phase24.A,Phase24.c,FourLogAffine.w,FourLogAffine.u,
    SharpLogRecurrence.lowerLog,SharpLogRecurrence.upperLog,alpha,beta,lam,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem actual_four_magnitude : (670908/1000000:ℝ) < 8*I10+8*I11 ∧
    8*I10+8*I11 < 713/1000 := by
  have hl : (670908/1000000:ℝ) < actualLower := by rw [actual_lower_exact]; norm_num
  exact ⟨hl.trans_le actual_four_lower,JFourRemainingMagnitude.actual_four_magnitude.2⟩

theorem actual_remaining_magnitude :
    0 ≤ JFourRemainingMagnitude.fourRemaining ∧
    JFourRemainingMagnitude.fourRemaining < 41218/1000000 := by
  have hc : remainingCap < (41218/1000000:ℝ) := by rw [remaining_cap_exact]; norm_num
  exact ⟨four_remaining_interval.1,four_remaining_interval.2.trans_lt hc⟩

/-- Its sign in Q is negative and its original multiplicity remains one quarter. -/
def motherGain : ℝ := (actualLower-FourTrueLowerTight.actualLower)/4

theorem mother_gain_exact : motherGain = 3230225186829114093431347298324867820329567/886883444521200649656437601192113522734560000 := by
  rw [motherGain,actual_lower_exact,FourTrueLowerTight.actual_lower_exact]
  norm_num

open SharpLogRecurrence JointLogTotalComparison TotalEndpointComparison
open FixedCoefficientUpperEnclosure (a b s)
open ClassicalAnalyticLeaves
open GlobalSignedActualComparison (packet mainLogs base jLower collected
  cancelled_actual_identity j_lower_identity log_two collection collected_payment)
def upperReal : ℝ :=
  (rationalPart+packet log+FifthActualIntegralRecovery.recurrenceCap+
    SixthFullRationalEnclosure.payment+1/100000+
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
  have h6 := SixthFullRationalEnclosure.sixth_log_loss_enclosure.2
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

def upperRational : ℝ := rationalTotal+
  (packet (fun _ => 0)+collected lowerLog V-logPayment-JointJLossStrength.fixedRecovery+
    FifthActualIntegralRecovery.recurrenceCap+SixthFullRationalEnclosure.payment+1/100000+
    Phase24.newFour-actualLower)/4+
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


/-- Exact substitution into the globally collected upper packet, not a new component sum. -/
theorem upper_substitution : upperRational = GlobalSignedActualComparison.upperRational-motherGain := by
  unfold upperRational GlobalSignedActualComparison.upperRational motherGain
  ring

def upperRemainder : ℝ := upperRational-8*lowerLog (5000/4469)

theorem remainder_substitution : upperRemainder = GlobalSignedActualComparison.upperRemainder-motherGain := by
  rw [upperRemainder,upper_substitution,GlobalSignedActualComparison.upperRemainder]
  ring

theorem upper_remainder_exact : upperRemainder = 2913026401587277341530419959229656030400680169826944767013291237291145612641710961868475509358649188495011046650038885182962845683543642046127721717430646993046022106424910280078625989194391588139995178656562326417099263287363087442798891385755957307717383611789211991012964901902323427093394133876377205028046878211559640249823789941538777/190438524288887818233515870106279625083950563556218761362634757081537311421125488654359784251996479154328309543988876256950910348253723528005420867343485269920661007415684728983211991212057975605102225863499409662791421568575969456295872410564995212959362550941765458650381261239171039600769694478861389966677243404593231364659619584000000000 := by
  rw [remainder_substitution,GlobalSignedActualComparison.upperRemainder_exact,mother_gain_exact]
  norm_num

theorem upper_rational_exact : upperRational = 1006673273153093333746228240345362300291549584395133520608315648561496716759153222434691196877283979759152317112130613911718108707076351763304614394164031253817213324925372990581430055049866543190865708814848616933104399003643924064078621882389785743733626921164473069928612458068715993104704487021032375056229058644482446905562360789/1102019354367131393288854225095491145714241143853907635090063189596239301579148501831211606073523622763169151125915154377973973498276059110090143829416528657621761003745828509814676922601677078855646607219576677562114433494245393409091245256770706627353304216829910626373299757779957514063078380431136007531040370779224812288000000000 := by
  have h := upper_remainder_exact
  unfold upperRemainder at h
  norm_num [lowerLog] at h
  linarith only [h]

theorem actual_Q_rational_bounds : (822040/1000000:ℝ) < JointHMotherPayment.unroundedCoefficient ∧
    JointHMotherPayment.unroundedCoefficient < 913481/1000000 := by
  have hu : upperRational < (913481/1000000:ℝ) := by rw [upper_rational_exact]; norm_num
  exact ⟨GlobalSignedActualComparison.actual_Q_rational_bounds.1,actual_upper.trans hu⟩

theorem upper_remainder_size : (15296/1000000:ℝ) < upperRemainder ∧
    upperRemainder < 15297/1000000 := by rw [upper_remainder_exact]; norm_num

/-- The improvement is real, but Four alone does not discharge the global remainder. -/
theorem gain_vs_global_remainder : 0 < motherGain ∧
    motherGain < GlobalSignedActualComparison.upperRemainder := by
  rw [mother_gain_exact,GlobalSignedActualComparison.upperRemainder_exact]
  norm_num

theorem actual_target_enclosure : -upperRemainder <
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient <
      GlobalSignedActualComparison.lowerRemainder := by
  have htL := log_lower (by norm_num : (1:ℝ) ≤ 5000/4469)
  constructor
  · unfold upperRemainder AnalyticTotalThreshold.target
    linarith only [actual_upper,htL]
  · exact GlobalSignedActualComparison.actual_target_enclosure.2

theorem actual_target_rational_bounds : (-15297/1000000:ℝ) <
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient ∧
    AnalyticTotalThreshold.target-JointHMotherPayment.unroundedCoefficient < 76146/1000000 := by
  constructor
  · linarith only [actual_target_enclosure.1,upper_remainder_size.2]
  · exact GlobalSignedActualComparison.actual_target_rational_bounds.2

theorem rational_endpoints_straddle :
    GlobalSignedActualComparison.lowerRational < 8*lowerLog (5000/4469) ∧
    8*V (5000/4469) < upperRational := by
  refine ⟨GlobalSignedActualComparison.rational_endpoints_straddle.1,?_⟩
  rw [upper_rational_exact]
  norm_num [V,upperLog,lowerLog]

end
end Wu2008DoubleSieve.BuchstabSeedTightLower
