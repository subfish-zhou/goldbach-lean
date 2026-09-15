import JointSixthFourDiagnostic

namespace Wu2008DoubleSieve.BaseGSharedActualRecovery
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure (a b s reciprocalPrimitive)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u pull AP)
open Phase23 (alphaModel gModel CP)
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Interval
noncomputable section

/-- Complete signed error kernel. The shared negative weight is collected first. -/
def kernel (p : ℝ → ℝ) (l r : ℝ) : ℝ :=
  ∫ t in l..r, (8-24*t)*(p (u t)/(t*(1/2-t))-ClassicalSingleBounds.g t)

theorem joint_exact (p P H : ℝ → ℝ) {l r : ℝ}
    (hl : a ≤ l) (hr : r ≤ s) (hlr : l ≤ r)
    (hp : Continuous p)
    (hP : ∀ v, 0 < v → HasDerivAt P (p v/v) v)
    (hH : ∀ t ∈ Icc l r, HasDerivAt H (p (u t)/(t*(1/2-t))) t)
    :
    24*(P (u l)-P (u r))-8*(H r-H l)+kernel p l r =
      24*(pull r-pull l)-8*(∫ t in l..r, ClassicalSingleBounds.g t) := by
  have ha := truncatedSixthLower_parameters.1
  have hr3 := hr.trans truncatedSixthLower_parameters.2.2.2.1.le
  have geom (t : ℝ) (ht : t ∈ Icc l r) : 0 < t ∧ 0 < 1/2-t ∧ 0 < u t := by
    have ht0 := ha.trans_le (hl.trans ht.1)
    have hd : 0 < 1/2-t := by linarith [ht.2.trans hr3]
    exact ⟨ht0,hd,div_pos hd ha⟩
  have hg := ClassicalSingleBounds.g_integrable hl hr3 hlr
  have htgi : IntervalIntegrable (fun t => t*ClassicalSingleBounds.g t) volume l r :=
    hg.continuousOn_mul continuousOn_id
  have hm : IntervalIntegrable (fun t => p (u t)/(t*(1/2-t))) volume l r := by
    apply ContinuousOn.intervalIntegrable
    apply (hp.comp (by unfold u; fun_prop)).continuousOn.div (by fun_prop)
    intro t ht
    rw [uIcc_of_le hlr] at ht
    exact mul_ne_zero (geom t ht).1.ne' (geom t ht).2.1.ne'
  have htm : IntervalIntegrable (fun t => t*(p (u t)/(t*(1/2-t)))) volume l r :=
    hm.continuousOn_mul continuousOn_id
  have ep : (∫ t in l..r, t*ClassicalSingleBounds.g t) = pull r-pull l := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ htgi
    intro t ht
    rw [uIcc_of_le hlr] at ht
    exact Phase22.pull_derivative ⟨hl.trans ht.1,ht.2.trans hr⟩
  have eP : (∫ t in l..r, t*(p (u t)/(t*(1/2-t)))) = P (u l)-P (u r) := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => -P (u t)) (fun t ht => ?_) htm
    · convert he using 1; ring
    rw [uIcc_of_le hlr] at ht
    have hd := ((hP (u t) (geom t ht).2.2).comp t
      (((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).div_const a)).neg
    convert hd using 1
    · rfl
    · dsimp [u]
      field_simp [ha.ne',(geom t ht).1.ne',(geom t ht).2.1.ne']
      ring
  have eH : (∫ t in l..r, p (u t)/(t*(1/2-t))) = H r-H l := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hm
    intro t ht
    exact hH t (uIcc_of_le hlr ▸ ht)
  have hk : kernel p l r =
      (8*(H r-H l)-24*(P (u l)-P (u r)))-
      (8*(∫ t in l..r, ClassicalSingleBounds.g t)-24*(pull r-pull l)) := by
    unfold kernel
    have he : (fun t => (8-24*t)*(p (u t)/(t*(1/2-t))-ClassicalSingleBounds.g t)) =
        (fun t => (8*(p (u t)/(t*(1/2-t)))-24*(t*(p (u t)/(t*(1/2-t)))))-
          (8*ClassicalSingleBounds.g t-24*(t*ClassicalSingleBounds.g t))) := by
      funext t; ring
    rw [he, intervalIntegral.integral_sub
      ((hm.const_mul 8).sub (htm.const_mul 24))
      ((hg.const_mul 8).sub (htgi.const_mul 24)),
      intervalIntegral.integral_sub (hm.const_mul 8) (htm.const_mul 24),
      intervalIntegral.integral_sub (hg.const_mul 8) (htgi.const_mul 24)]
    simp only [intervalIntegral.integral_const_mul,eH,eP,ep]
  linarith only [hk]

theorem affine_exact (j C d : ℝ) {l r : ℝ}
    (hl : a ≤ l) (hr : r ≤ s) (hlr : l ≤ r)
    :
    24*(BaseRecurrenceLower.P j C d (u l)-BaseRecurrenceLower.P j C d (u r))-
      8*(AP j C d r-AP j C d l)+kernel (fun v => C+d*(v-j)) l r =
      24*(pull r-pull l)-8*(∫ t in l..r, ClassicalSingleBounds.g t) := by
  apply joint_exact (fun v => C+d*(v-j)) (BaseRecurrenceLower.P j C d) (AP j C d)
    hl hr hlr (by fun_prop) (fun v hv => BaseRecurrenceLower.P_derivative j C d hv.ne')
  intro t ht
  have ht0 := truncatedSixthLower_parameters.1.trans_le (hl.trans ht.1)
  have ht1 : t < 1/2 := by linarith [ht.2.trans (hr.trans truncatedSixthLower_parameters.2.2.2.1.le)]
  convert! ((GVariableIntegral.reciprocal_derivative ht0 ht1).const_mul C).add
    ((GVariableIntegral.affine_derivative (j := j) ht0 ht1).const_mul d) using 1
  dsimp [u]
  ring

theorem cubic_exact :
    24*(CP 4-CP 3)-8*(VariableGIntegral.primitive s-VariableGIntegral.primitive (c 4)) +
      kernel VariableUpperEnvelope.cubic (c 4) s =
      24*(pull s-pull (c 4))-8*(∫ t in c 4..s, ClassicalSingleBounds.g t) := by
  have hl : a ≤ c 4 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hlr : c 4 ≤ s := by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hu4 : u (c 4) = 4 := by norm_num [u,a,c,truncatedSixthLowerAlpha]
  have hu3 : u s = 3 := by norm_num [u,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  suffices h : 24*(CP (u (c 4))-CP (u s))-8*(VariableGIntegral.primitive s-VariableGIntegral.primitive (c 4)) +
      kernel VariableUpperEnvelope.cubic (c 4) s =
      24*(pull s-pull (c 4))-8*(∫ t in c 4..s, ClassicalSingleBounds.g t) by
    simpa only [hu4,hu3] using h
  apply joint_exact VariableUpperEnvelope.cubic CP VariableGIntegral.primitive
    hl le_rfl hlr (by unfold VariableUpperEnvelope.cubic; fun_prop)
    (fun v hv => Phase23.CP_derivative hv.ne')
  · intro t ht
    exact VariableGIntegral.derivative
      (truncatedSixthLower_parameters.1.trans_le (hl.trans ht.1)).ne'
      (by linarith [ht.2,truncatedSixthLower_parameters.2.2.2.1])

/-- The three unchanged recurrence intervals, with the old shared payment removed. -/
def highKernel : ℝ := kernel (fun v => (42823/151875)*v) a (c 5)
def middleKernel : ℝ := kernel (fun v => GConvexChord.C+GConvexChord.m*v) (c 5) (c 4)
def lowKernel : ℝ := kernel VariableUpperEnvelope.cubic (c 4) s-SharedRationalEnvelope.deltaShared

theorem shared_exact : AnalyticTotalThreshold.sharedLoss = highKernel+middleKernel+lowKernel := by
  unfold AnalyticTotalThreshold.sharedLoss
  have h5 : a ≤ c 5 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have h54 : c 5 ≤ c 4 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have h4s : c 4 ≤ s := by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hs3 := truncatedSixthLower_parameters.2.2.2.1.le
  have j5 := affine_exact 0 0 (42823/151875) le_rfl (h54.trans h4s) h5
  have j4 := affine_exact 0 GConvexChord.C GConvexChord.m h5 h4s h54
  have jq := cubic_exact
  have i5 := ClassicalSingleBounds.g_integrable le_rfl ((h54.trans h4s).trans hs3) h5
  have i4 := ClassicalSingleBounds.g_integrable h5 (h4s.trans hs3) h54
  have iq := ClassicalSingleBounds.g_integrable (h5.trans h54) hs3 h4s
  have ih := ClassicalSingleBounds.g_integrable (h5.trans (h54.trans h4s)) le_rfl hs3
  have e1 := intervalIntegral.integral_add_adjacent_intervals i5 i4
  have e2 := intervalIntegral.integral_add_adjacent_intervals (i5.trans i4) iq
  have e3 := intervalIntegral.integral_add_adjacent_intervals ((i5.trans i4).trans iq) ih
  have eh := ClassicalSingleBounds.high_integral_eq
  have erec : reciprocalPrimitive (1/3)-reciprocalPrimitive s = 2*log (6*a/s) := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := reciprocalPrimitive) (fun t ht => ?_) ih
    · linarith
    rw [uIcc_of_le hs3] at ht
    rw [ClassicalSingleBounds.g_high ht]
    exact GVariableIntegral.reciprocal_derivative
      (truncatedSixthLower_parameters.1.trans_le ((h5.trans (h54.trans h4s)).trans ht.1))
      (by linarith [ht.2])
  have g1 : SingleUpperClassicalLimit.Glin (1/3) = 4*∫ t in a..(1/3 : ℝ), ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,ClassicalSingleBounds.g,ClassicalSingleBounds.a,a]
  have g2 : SingleUpperClassicalLimit.Glin s = 4*∫ t in a..s, ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,ClassicalSingleBounds.g,ClassicalSingleBounds.a,a]
  have pa : pull a = -wuLowerCoefficient (1/(2*a)) := by
    norm_num [pull,u,a,truncatedSixthLowerAlpha]
  have ps : pull s = -log 3 := by
    have hs : u s+1=4 := by norm_num [u,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
    rw [pull,hs,BaseRecurrenceLower.lower_four_value]
  have us : u (c 5)=5 ∧ u (c 4)=4 ∧ u a=1127/200 := by
    norm_num [u,a,c,truncatedSixthLowerAlpha]
  rw [us.1,us.2.2] at j5
  rw [us.1,us.2.1] at j4
  rw [pa] at j5
  rw [ps] at jq
  rw [g1,g2]
  have eh5 : AP 0 0 (42823/151875) (c 5)-AP 0 0 (42823/151875) a =
      (42823/151875)/a*log (c 5/a) := by
    rw [log_div (truncatedSixthLower_parameters.1.trans_le h5).ne' truncatedSixthLower_parameters.1.ne']
    unfold AP GVariableIntegral.affinePrimitive
    norm_num [c]
    ring
  have eh4 : AP 0 GConvexChord.C GConvexChord.m (c 4)-AP 0 GConvexChord.C GConvexChord.m (c 5) = GConvexChord.endpoint := by
    rw [← GConvexChord.primitive_endpoint]
    unfold AP GVariableIntegral.affinePrimitive reciprocalPrimitive GConvexChord.primitive
    norm_num [c,VariableGIntegral.c,SharpSingleBalance.c,SharpSingleBalance.a,VariableGIntegral.a]
    ring
  rw [eh5] at j5
  rw [eh4] at j4
  dsimp [BaseRecurrenceLower.P] at j5
  dsimp [alphaModel,gModel,highKernel,middleKernel,lowKernel]
  simp only [mul_sub, sub_zero, zero_add] at j5 j4
  norm_num [a,ClassicalSingleBounds.a,ClassicalSingleBounds.s,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma] at j5 j4 jq e1 e2 e3 eh ⊢
  linarith


/-- No discarded residual is silently paid a second time. -/
theorem three_exact : AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+
    AnalyticTotalThreshold.sharedLoss =
    AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+
      highKernel+middleKernel+lowKernel := by
  rw [shared_exact]; ring

/-- Integrability of the full signed discrepancy, not an absolute-error bound. -/
theorem kernel_integrable (p : ℝ → ℝ) {l r : ℝ}
    (hl : a ≤ l) (hr : r ≤ s) (hlr : l ≤ r) (hp : Continuous p) :
    IntervalIntegrable (fun t => (8-24*t)*(p (u t)/(t*(1/2-t))-
      ClassicalSingleBounds.g t)) volume l r := by
  have hg := ClassicalSingleBounds.g_integrable hl
    (hr.trans truncatedSixthLower_parameters.2.2.2.1.le) hlr
  have hm : IntervalIntegrable (fun t => p (u t)/(t*(1/2-t))) volume l r := by
    apply ContinuousOn.intervalIntegrable
    apply (hp.comp (by unfold u; fun_prop)).continuousOn.div (by fun_prop)
    intro t ht
    rw [uIcc_of_le hlr] at ht
    have ht0 := truncatedSixthLower_parameters.1.trans_le (hl.trans ht.1)
    have hd : 0 < 1/2-t := by linarith [ht.2,hr,truncatedSixthLower_parameters.2.2.2.1]
    exact (mul_pos ht0 hd).ne'
  exact (hm.sub hg).continuousOn_mul (by fun_prop)

theorem high_nonnegative : 0 ≤ highKernel := by
  apply intervalIntegral.integral_nonneg (by norm_num [a,c,truncatedSixthLowerAlpha])
  intro t ht
  have ht0 : 0 < t := truncatedSixthLower_parameters.1.trans_le ht.1
  have hd : 0 < 1/2-t := by norm_num [c,a,truncatedSixthLowerAlpha] at ht; linarith
  have hu : 5 ≤ u t := by
    apply (le_div_iff₀ truncatedSixthLower_parameters.1).2
    have h : t ≤ 1/2-5*a := ht.2
    linarith
  have hh := (SharpSingleBalance.upper_ratio_antitone (by norm_num : (0:ℝ)<5) hu).trans
    SharpLogRecurrence.upper_five_div
  have hb := (div_le_iff₀ (by linarith : 0 < u t)).1 hh
  have hn : 0 ≤ 8-24*t := by norm_num [c,a,truncatedSixthLowerAlpha] at ht; linarith
  apply mul_nonneg hn
  apply sub_nonneg.mpr
  change wuUpperCoefficient (u t)/(t*(1/2-t)) ≤ _
  apply div_le_div_of_nonneg_right _ (mul_pos ht0 hd).le
  linarith

theorem low_nonnegative : 0 ≤ lowKernel := by
  have hc := cubic_exact
  have hp := SharedRationalEnvelope.cubic_joint_gain
  unfold lowKernel
  linarith only [hc,hp]

/-- The already-paid cubic-to-rational gap disappears exactly from the low kernel. -/
theorem low_explicit : lowKernel = ∫ t in c 4..s,
    SharedRationalEnvelope.weight t*(SharedRationalEnvelope.p (u t)-wuUpperCoefficient (u t)) := by
  have h := SharedRationalEnvelope.window_order
  have hk := kernel_integrable VariableUpperEnvelope.cubic h.1 le_rfl h.2.1
    (by unfold VariableUpperEnvelope.cubic; fun_prop)
  have hd : IntervalIntegrable SharedRationalEnvelope.gainDensity volume (c 4) s :=
    SharedRationalEnvelope.density_continuous.intervalIntegrable_of_Icc h.2.1
  unfold lowKernel kernel SharedRationalEnvelope.deltaShared
  rw [← intervalIntegral.integral_sub hk hd]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp [SharedRationalEnvelope.gainDensity,SharedRationalEnvelope.weight,
    ClassicalSingleBounds.g,ClassicalSingleBounds.a,u,a]
  ring

/-- The original curvature, integrated against its correct signed net weight. -/
def curvatureDensity (t : ℝ) : ℝ := (8-24*t)*GCurvatureChord.deficit t
def curvaturePrimitive (t : ℝ) : ℝ :=
  (6*t^4+(-8-24*(c 4+c 5))*t^3/3+
    (4*(c 4+c 5)+12*c 4*c 5)*t^2-8*c 4*c 5*t)/(9*a^2)
def recovery : ℝ := (8-12*(c 4+c 5))*a/54

theorem curvature_derivative (t : ℝ) :
    HasDerivAt curvaturePrimitive (curvatureDensity t) t := by
  convert ((((((hasDerivAt_id t).pow 4).const_mul 6).add
    ((((hasDerivAt_id t).pow 3).const_mul (-8-24*(c 4+c 5))).div_const 3)).add
    (((hasDerivAt_id t).pow 2).const_mul (4*(c 4+c 5)+12*c 4*c 5))).sub
    ((hasDerivAt_id t).const_mul (8*c 4*c 5))).div_const (9*a^2) using 1 <;>
    first | rfl | (dsimp [curvatureDensity,GCurvatureChord.deficit,
      VariableGIntegral.c,SharpSingleBalance.c,SharpSingleBalance.a,VariableGIntegral.a,c,a]; ring)

theorem curvature_ftc : (∫ t in c 5..c 4, curvatureDensity t) = recovery := by
  have hi : Continuous curvatureDensity := by
    unfold curvatureDensity GCurvatureChord.deficit; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => curvature_derivative t) (hi.intervalIntegrable _ _)]
  norm_num [curvaturePrimitive,recovery,c,a,truncatedSixthLowerAlpha]

theorem middle_recovery : recovery ≤ middleKernel := by
  have hg := GConvexChord.geometry
  have hk := kernel_integrable (fun v => GConvexChord.C+GConvexChord.m*v)
    hg.2.1 hg.2.2.2.1 hg.2.2.1 (by fun_prop)
  have hi : Continuous curvatureDensity := by
    unfold curvatureDensity GCurvatureChord.deficit; fun_prop
  have hm := intervalIntegral.integral_mono_on hg.2.2.1
    (hi.intervalIntegrable _ _) hk (fun t ht => ?_)
  · have he : (∫ t in VariableGIntegral.c 5..VariableGIntegral.c 4, curvatureDensity t) = recovery := by
      convert curvature_ftc using 1
      all_goals
        norm_num [VariableGIntegral.c,SharpSingleBalance.c,SharpSingleBalance.a,c,a,truncatedSixthLowerAlpha]
    rw [he] at hm
    convert hm using 1
    all_goals
      norm_num [middleKernel,kernel,VariableGIntegral.c,SharpSingleBalance.c,SharpSingleBalance.a,c,a,truncatedSixthLowerAlpha]
  have hn : 0 ≤ 8-24*t := by
    have hs := ht.2.trans hg.2.2.2.1 |>.trans hg.2.2.2.2
    linarith
  have h := GCurvatureChord.pointwise_joint ht
  have geom := GCurvatureChord.segment_domain ht
  have he : (GConvexChord.C+GConvexChord.m*u t)/(t*(1/2-t)) = GConvexChord.majorant t := by
    have hd2 : 1-t*2 ≠ 0 := by linarith [geom.2.1]
    dsimp [GConvexChord.majorant,u]
    field_simp [geom.1.ne',geom.2.1.ne',hd2]
    ring_nf
    field_simp [hd2]
    ring
  dsimp [curvatureDensity]
  rw [he]
  exact mul_le_mul_of_nonneg_left (by linarith only [h]) hn

theorem recovery_exact : recovery = (274600/47545083 : ℝ) := by
  norm_num [recovery,c,a,truncatedSixthLowerAlpha]

theorem shared_recovery : recovery ≤ AnalyticTotalThreshold.sharedLoss := by
  rw [shared_exact]
  linarith only [middle_recovery,high_nonnegative,low_nonnegative]

/-- The beta recurrence remainder is kept rather than replaced by zero. -/
def betaKernel : ℝ := ∫ v in (3:ℝ)..(78/25:ℝ),
  (wuUpperCoefficient v-(1+(v-3)^2/9))/v

theorem beta_exact : wuLowerCoefficient (1/(2*b)) =
    log 3+(BaseRecurrenceLower.Q (78/25)-BaseRecurrenceLower.Q 3)+betaKernel := by
  have hu := wuUpperCoefficient_div_intervalIntegrable (by norm_num : (0:ℝ)<3)
    (by norm_num : (3:ℝ)≤78/25)
  have hq := BaseRecurrenceLower.polynomial_div_integrable
    (fun v : ℝ => 1+(v-3)^2/9) (by fun_prop)
    (by norm_num : (0:ℝ)<3) (by norm_num : (3:ℝ)≤78/25)
  have hr := wuLowerCoefficient_sub_eq_integral (by norm_num : (2:ℝ)≤4)
    (by norm_num [b,truncatedSixthLowerBeta] : 4≤1/(2*b))
  have hQ := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => BaseRecurrenceLower.Q_derivative (by
      rw [uIcc_of_le (by norm_num : (3:ℝ)≤78/25)] at hv
      linarith [hv.1])) hq
  have he : betaKernel = (∫ v in (3:ℝ)..(78/25:ℝ), wuUpperCoefficient v/v)-
      (BaseRecurrenceLower.Q (78/25)-BaseRecurrenceLower.Q 3) := by
    unfold betaKernel
    simp_rw [sub_div]
    rw [intervalIntegral.integral_sub hu hq,hQ]
  norm_num only [show (4:ℝ)-1=3 by norm_num,
    show 1/(2*b)-1=(78/25:ℝ) by norm_num [b,truncatedSixthLowerBeta],
    BaseRecurrenceLower.lower_four_value] at hr
  linarith only [hr,he]

def baseLogRemainder : ℝ := 32*(log (3/2)-lowerLog (3/2))+
  16*(log (26/25)-lowerLog (26/25))
def gLogRemainder : ℝ :=
  (8/a)*(42823/151875)*(upperLog (c 5/a)-log (c 5/a))+
  8*(GConvexChord.m/a+2*GConvexChord.C)*(upperLog (c 4/c 5)-log (c 4/c 5))+
  8*VariableGIntegral.logCoefficient*(upperLog (s/c 4)-log (s/c 4))+
  8*(upperLog (6*a/s)-log (6*a/s))

theorem base_exact : AnalyticTotalThreshold.baseLoss = baseLogRemainder+8*betaKernel := by
  unfold AnalyticTotalThreshold.baseLoss
  rw [beta_exact]
  unfold alphaModel Phase23.modelBase SignedTotalCorrelation.e2
    SignedTotalCorrelation.e43 SignedTotalCorrelation.e54 baseLogRemainder
  rw [Phase23.CP_difference (by norm_num) (by norm_num),
    BaseRecurrenceLower.P_difference 0 GConvexChord.C GConvexChord.m (by norm_num) (by norm_num),
    BaseRecurrenceLower.Q_difference (by norm_num) (by norm_num)]
  have h := SharpJBalance.log_split_two (by norm_num : (0:ℝ)<3)
  norm_num [lowerLog] at h ⊢
  linarith only [h]

theorem g_exact : AnalyticTotalThreshold.gLoss = gLogRemainder := by
  unfold AnalyticTotalThreshold.gLoss gModel
  change GConvexChord.rationalG-88*(SignedTotalCorrelation.d43-SignedTotalCorrelation.e43)-
    16*GConvexChord.C*(SignedTotalCorrelation.d54-SignedTotalCorrelation.e54)-
    ((8/a)*(42823/151875)*log (c 5/a)+8*GConvexChord.endpoint+
    8*(VariableGIntegral.primitive VariableGIntegral.s-VariableGIntegral.primitive (VariableGIntegral.c 4))+
    8*log (6*a/s)) = _
  rw [VariableGIntegral.endpoint]
  unfold GConvexChord.rationalG GConvexChord.endpoint gLogRemainder
    SignedTotalCorrelation.d43 SignedTotalCorrelation.e43 SignedTotalCorrelation.d54 SignedTotalCorrelation.e54
  dsimp [VariableGIntegral.c,SharpSingleBalance.c,SharpSingleBalance.a,c,a]
  ring

/-- Complete recovery: every original B/G/shared error survives explicitly. -/
theorem complete_three_kernel :
    AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+AnalyticTotalThreshold.sharedLoss =
    baseLogRemainder+gLogRemainder+8*betaKernel+highKernel+middleKernel+lowKernel := by
  rw [base_exact,g_exact,shared_exact]; ring

/-- Stronger certificate in the same seven-error identity; Q is unchanged. -/
def coefficient : ℝ := JointSixthFourDiagnostic.coefficient+recovery/4

theorem coefficient_le_actual : coefficient ≤ JointHMotherPayment.unroundedCoefficient := by
  have hgap := AnalyticTotalThreshold.actual_gap_identity
  rw [AnalyticTotalThreshold.signed_loss_identity] at hgap
  have hs := AnalyticTotalThreshold.signed_losses_nonnegative
  have hl := AnalyticTotalThreshold.losses_nonnegative
  have hj := JointJLossStrength.actual_jLoss_lower
  have h6 := ClassicalLossBottleneck.sixth_recurrence_integral_cap.1
  have h4 := FourActualCapRecovery.actual_fourLoss_lower
  have hb := shared_recovery
  unfold coefficient JointSixthFourDiagnostic.coefficient ClassicalLossBottleneck.recoveredCoefficient
  unfold AnalyticTotalThreshold.sixthLoss at hgap h6
  linarith only [hgap,hs.1,hs.2.1,hl.2.1,hj,h6,h4,hb]

theorem coefficient_gain_exact : coefficient-JointSixthFourDiagnostic.coefficient =
    (68650/47545083 : ℝ) := by
  unfold coefficient
  rw [recovery_exact]
  ring

/-- The exact first upper recurrence, containing logarithms only. -/
def initialUpper (v : ℝ) : ℝ := 1+∫ x in (2:ℝ)..(v-1), log (x-1)/x

theorem upper_initial_exact {v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    wuUpperCoefficient v = initialUpper v := by
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2:ℝ)≤3) hv
  have he : wuUpperCoefficient 3 = 1 :=
    jr1965F_normalized_initial
      (by norm_num) le_rfl
  have hi : (∫ x in (2:ℝ)..(v-1), wuLowerCoefficient x/x) =
      ∫ x in (2:ℝ)..(v-1), log (x-1)/x := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [uIcc_of_le (by linarith : (2:ℝ)≤v-1)] at hx
    rw [show wuLowerCoefficient x = log (x-1) from
      jr1965f_normalized_firstInterval
        hx.1 (by linarith [hx.2])]
  norm_num only [show (3:ℝ)-1=2 by norm_num,he] at hr
  rw [hi] at hr
  unfold initialUpper
  linarith only [hr]

/-- Beyond four, the lower surplus is an exact iterated log kernel. -/
def lowerLogKernel (x : ℝ) : ℝ := ∫ z in (3:ℝ)..(x-1), (initialUpper z-1)/z

theorem lower_log_kernel_exact {x : ℝ} (hx : 4 ≤ x) (hx5 : x ≤ 5) :
    wuLowerCoefficient x = log (x-1)+lowerLogKernel x := by
  have hr := wuLowerCoefficient_sub_eq_integral (by norm_num : (2:ℝ)≤4) hx
  have hz : (3:ℝ)≤x-1 := by linarith
  have hu := wuUpperCoefficient_div_intervalIntegrable (by norm_num : (0:ℝ)<3) hz
  have hi : IntervalIntegrable (fun z : ℝ => 1/z) volume 3 (x-1) := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div continuousOn_id (fun z hz' => by
      rw [uIcc_of_le hz] at hz'
      change z ≠ 0
      linarith [hz'.1])
  have hk : lowerLogKernel x = (∫ z in (3:ℝ)..(x-1), wuUpperCoefficient z/z)-
      (log (x-1)-log 3) := by
    unfold lowerLogKernel
    calc
      _ = ∫ z in (3:ℝ)..(x-1), wuUpperCoefficient z/z-1/z := by
        apply intervalIntegral.integral_congr
        intro z hz'
        dsimp only
        rw [uIcc_of_le hz] at hz'
        rw [upper_initial_exact hz'.1 (by linarith [hz'.2])]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub hu hi,
          integral_reciprocal (by norm_num) hz]
  norm_num only [show (4:ℝ)-1=3 by norm_num,BaseRecurrenceLower.lower_four_value] at hr
  linarith only [hr,hk]

/-- Explicit original delay continuation. The sole branch is the old initial endpoint four. -/
def explicitUpper (v : ℝ) : ℝ := 1+∫ x in (2:ℝ)..(v-1),
  (log (x-1)+(if x ≤ 4 then 0 else lowerLogKernel x))/x

theorem upper_explicit_exact {v : ℝ} (hv : 3 ≤ v) (hvc : v ≤ 1127/200) :
    wuUpperCoefficient v = explicitUpper v := by
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2:ℝ)≤3) hv
  have he : wuUpperCoefficient 3 = 1 :=
    jr1965F_normalized_initial
      (by norm_num) le_rfl
  have hi : (∫ x in (2:ℝ)..(v-1), wuLowerCoefficient x/x) =
      ∫ x in (2:ℝ)..(v-1), (log (x-1)+(if x ≤ 4 then 0 else lowerLogKernel x))/x := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [uIcc_of_le (by linarith : (2:ℝ)≤v-1)] at hx
    by_cases h4 : x ≤ 4
    · rw [if_pos h4,add_zero]
      rw [show wuLowerCoefficient x = log (x-1) from
        jr1965f_normalized_firstInterval hx.1 h4]
    · rw [if_neg h4,lower_log_kernel_exact (by linarith) (by linarith [hx.2])]
  norm_num only [show (3:ℝ)-1=2 by norm_num,he] at hr
  rw [hi] at hr
  unfold explicitUpper
  linarith only [hr]

/-- Log-only full kernel; no sampling, quadrature, or new Taylor term. -/
def explicitKernel (p : ℝ → ℝ) (l r : ℝ) : ℝ :=
  ∫ t in l..r, SharedRationalEnvelope.weight t*(p (u t)-explicitUpper (u t))

theorem kernel_explicit (p : ℝ → ℝ) {l r : ℝ}
    (hl : a ≤ l) (hr : r ≤ s) (hlr : l ≤ r) : kernel p l r = explicitKernel p l r := by
  unfold kernel explicitKernel
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hlr] at ht
  have h3 : 3 ≤ u t := by
    apply (le_div_iff₀ truncatedSixthLower_parameters.1).2
    have h : t ≤ 1/2-3*a := ht.2.trans hr
    linarith
  have htop : u t ≤ 1127/200 := by
    apply (div_le_iff₀ truncatedSixthLower_parameters.1).2
    have h := hl.trans ht.1
    norm_num [a,truncatedSixthLowerAlpha] at h ⊢
    linarith only [h]
  change (8-24*t)*(p (u t)/(t*(1/2-t))-wuUpperCoefficient (u t)/(t*(1/2-t))) = _
  rw [upper_explicit_exact h3 htop]
  unfold SharedRationalEnvelope.weight
  ring

/-- Literal whole-triple log-integral identity, keeping the old payment exactly once. -/
theorem complete_log_kernel :
    AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+AnalyticTotalThreshold.sharedLoss =
    baseLogRemainder+gLogRemainder+
    8*(∫ v in (3:ℝ)..(78/25:ℝ), (initialUpper v-(1+(v-3)^2/9))/v)+
    explicitKernel (fun v => (42823/151875)*v) a (c 5)+
    explicitKernel (fun v => GConvexChord.C+GConvexChord.m*v) (c 5) (c 4)+
    explicitKernel VariableUpperEnvelope.cubic (c 4) s-SharedRationalEnvelope.deltaShared := by
  rw [complete_three_kernel]
  have hg := GConvexChord.geometry
  have he : betaKernel = ∫ v in (3:ℝ)..(78/25:ℝ), (initialUpper v-(1+(v-3)^2/9))/v := by
    unfold betaKernel
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [uIcc_of_le (by norm_num : (3:ℝ)≤78/25)] at hv
    rw [upper_initial_exact hv.1 (by linarith [hv.2])]
  rw [he]
  unfold highKernel middleKernel lowKernel
  rw [kernel_explicit _ le_rfl (by norm_num [c,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
    (by norm_num [c,a,truncatedSixthLowerAlpha]),
    kernel_explicit _ (by norm_num [c,a,truncatedSixthLowerAlpha])
      (by norm_num [c,s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
      (by norm_num [c,a,truncatedSixthLowerAlpha]),
    kernel_explicit _ SharedRationalEnvelope.window_order.1 le_rfl SharedRationalEnvelope.window_order.2.1]
  ring

/-- All unpaid mass remains visible after the new signed curvature payment. -/
def unpaidTriple : ℝ := baseLogRemainder+gLogRemainder+8*betaKernel+
  highKernel+(middleKernel-recovery)+lowKernel

theorem unpaid_triple_exact : unpaidTriple =
    AnalyticTotalThreshold.baseLoss+AnalyticTotalThreshold.gLoss+
      AnalyticTotalThreshold.sharedLoss-recovery := by
  rw [complete_three_kernel]
  unfold unpaidTriple
  ring

theorem unpaid_triple_nonnegative : 0 ≤ unpaidTriple := by
  rw [unpaid_triple_exact]
  have h := AnalyticTotalThreshold.signed_losses_nonnegative
  linarith only [h.1,h.2.1,shared_recovery]

/-- Same Q, same seven errors, now with the full B/G/shared kernel retained. -/
theorem seven_error_exact : JointHMotherPayment.unroundedCoefficient-coefficient =
    (unpaidTriple+(AnalyticTotalThreshold.jLoss-JointJLossStrength.recovery)+
      AnalyticTotalThreshold.fifthLoss+
      (truncatedSixthLowerF6lin-ClassicalLossBottleneck.sixthLogIntegral)+
      (AnalyticTotalThreshold.fourLoss-FourActualCapRecovery.recovery))/4 := by
  have h := AnalyticTotalThreshold.actual_gap_identity
  rw [AnalyticTotalThreshold.signed_loss_identity] at h
  rw [unpaid_triple_exact]
  unfold coefficient JointSixthFourDiagnostic.coefficient ClassicalLossBottleneck.recoveredCoefficient
  unfold AnalyticTotalThreshold.sixthLoss at h
  linarith only [h]

end
end Wu2008DoubleSieve.BaseGSharedActualRecovery
