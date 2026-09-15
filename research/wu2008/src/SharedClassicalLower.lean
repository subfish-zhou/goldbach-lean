import ClassicalSignedBounds

namespace Wu2008DoubleSieve.Phase23
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure (a b s reciprocalPrimitive)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u pull AP)
open scoped Interval
noncomputable section

theorem joint_segment (p P H : ℝ → ℝ) {l r : ℝ}
    (hl : a ≤ l) (hr : r ≤ s) (hlr : l ≤ r)
    (hp : Continuous p)
    (hP : ∀ v, 0 < v → HasDerivAt P (p v/v) v)
    (hH : ∀ t ∈ Icc l r, HasDerivAt H (p (u t)/(t*(1/2-t))) t)
    (hbound : ∀ t ∈ Icc l r, wuUpperCoefficient (u t) ≤ p (u t)) :
    24*(P (u l)-P (u r))-8*(H r-H l) ≤
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
  have hc := intervalIntegral.integral_mono_on hlr
    ((htm.const_mul 24).sub (hm.const_mul 8))
    ((htgi.const_mul 24).sub (hg.const_mul 8)) (fun t ht => by
      have h := div_le_div_of_nonneg_right (hbound t ht)
        (mul_pos (geom t ht).1 (geom t ht).2.1).le
      have hn : 24*t-8 ≤ 0 := by linarith [ht.2.trans hr3]
      have hh := mul_le_mul_of_nonpos_left h hn
      change _ ≤ (24*t-8)*ClassicalSingleBounds.g t at hh
      nlinarith only [hh])
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
  rw [intervalIntegral.integral_sub (htgi.const_mul 24) (hg.const_mul 8),
    intervalIntegral.integral_sub (htm.const_mul 24) (hm.const_mul 8),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,ep,eP,eH] at hc
  exact hc

theorem affine_joint (j C d : ℝ) {l r : ℝ}
    (hl : a ≤ l) (hr : r ≤ s) (hlr : l ≤ r)
    (hb : ∀ t ∈ Icc l r, wuUpperCoefficient (u t) ≤ C+d*(u t-j)) :
    24*(BaseRecurrenceLower.P j C d (u l)-BaseRecurrenceLower.P j C d (u r))-
      8*(AP j C d r-AP j C d l) ≤
      24*(pull r-pull l)-8*(∫ t in l..r, ClassicalSingleBounds.g t) := by
  apply joint_segment (fun v => C+d*(v-j)) (BaseRecurrenceLower.P j C d) (AP j C d)
    hl hr hlr (by fun_prop) (fun v hv => BaseRecurrenceLower.P_derivative j C d hv.ne') _ hb
  intro t ht
  have ht0 := truncatedSixthLower_parameters.1.trans_le (hl.trans ht.1)
  have ht1 : t < 1/2 := by linarith [ht.2.trans (hr.trans truncatedSixthLower_parameters.2.2.2.1.le)]
  convert! ((GVariableIntegral.reciprocal_derivative ht0 ht1).const_mul C).add
    ((GVariableIntegral.affine_derivative (j := j) ht0 ht1).const_mul d) using 1
  dsimp [u]
  ring

def CP (v : ℝ) : ℝ := (11/2)*log v-(15/4)*v+v^2/2-v^3/36

theorem CP_derivative {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt CP (VariableUpperEnvelope.cubic v/v) v := by
  convert ((((hasDerivAt_log hv).const_mul (11/2)).sub
    ((hasDerivAt_id v).const_mul (15/4))).add
    (((hasDerivAt_id v).pow 2).div_const 2)).sub
    (((hasDerivAt_id v).pow 3).div_const 36) using 1 <;>
    first | rfl | (dsimp [VariableUpperEnvelope.cubic]; field_simp; ring)

theorem CP_difference {l r : ℝ} (hl : l ≠ 0) (hr : r ≠ 0) :
    CP r-CP l = (11/2)*log (r/l)-(15/4)*(r-l)+(r^2-l^2)/2-(r^3-l^3)/36 := by
  rw [log_div hr hl]
  unfold CP
  ring

theorem cubic_joint :
    24*(CP 4-CP 3)-8*(VariableGIntegral.primitive s-VariableGIntegral.primitive (c 4)) ≤
      24*(pull s-pull (c 4))-8*(∫ t in c 4..s, ClassicalSingleBounds.g t) := by
  have hl : a ≤ c 4 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hlr : c 4 ≤ s := by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hu4 : u (c 4) = 4 := by norm_num [u,a,c,truncatedSixthLowerAlpha]
  have hu3 : u s = 3 := by norm_num [u,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  suffices h : 24*(CP (u (c 4))-CP (u s))-8*(VariableGIntegral.primitive s-VariableGIntegral.primitive (c 4)) ≤
      24*(pull s-pull (c 4))-8*(∫ t in c 4..s, ClassicalSingleBounds.g t) by
    simpa only [hu4,hu3] using h
  apply joint_segment VariableUpperEnvelope.cubic CP VariableGIntegral.primitive
    hl le_rfl hlr (by unfold VariableUpperEnvelope.cubic; fun_prop)
    (fun v hv => CP_derivative hv.ne')
  · intro t ht
    exact VariableGIntegral.derivative
      (truncatedSixthLower_parameters.1.trans_le (hl.trans ht.1)).ne'
      (by linarith [ht.2,truncatedSixthLower_parameters.2.2.2.1])
  · intro t ht
    apply VariableUpperEnvelope.upper_cubic
    · apply (le_div_iff₀ truncatedSixthLower_parameters.1).2
      have h : t ≤ 1/2-3*a := ht.2
      linarith
    · apply (div_le_iff₀ truncatedSixthLower_parameters.1).2
      have h : 1/2-4*a ≤ t := ht.1
      linarith

def alphaModel : ℝ := log 3+(CP 4-CP 3)+
  (BaseRecurrenceLower.P 0 GConvexChord.C GConvexChord.m 5-BaseRecurrenceLower.P 0 GConvexChord.C GConvexChord.m 4)+
  (42823/151875)*(1127/200-5)

def gModel : ℝ := (8/a)*(42823/151875)*log (c 5/a)+8*GConvexChord.endpoint+
  8*(VariableGIntegral.primitive s-VariableGIntegral.primitive (c 4))+8*log (6*a/s)

/-- Reverse the shared envelope before any rational payment; no independent base bound. -/
theorem shared_actual_lower :
    24*alphaModel-gModel ≤ 24*wuLowerCoefficient (1/(2*a))-
      (SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s) := by
  have h5 : a ≤ c 5 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have h54 : c 5 ≤ c 4 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have h4s : c 4 ≤ s := by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hs3 := truncatedSixthLower_parameters.2.2.2.1.le
  have j5 := affine_joint 0 0 (42823/151875) le_rfl (h54.trans h4s) h5 (fun t ht => by
    have hu : 5 ≤ u t := by
      apply (le_div_iff₀ truncatedSixthLower_parameters.1).2
      have hh : t ≤ 1/2-5*a := ht.2
      linarith
    have hh := SharpSingleBalance.upper_ratio_antitone (by norm_num : (0 : ℝ) < 5) hu
    have h := hh.trans SharpLogRecurrence.upper_five_div
    have hu0 : 0 < u t := by linarith
    have h' := (div_le_iff₀ hu0).1 h
    linarith)
  have j4 := affine_joint 0 GConvexChord.C GConvexChord.m h5 h4s h54 (fun t ht => by
    have h := GConvexChord.upper_chord (GCurvatureChord.segment_domain ht).2.2
    change wuUpperCoefficient (u t) ≤ GConvexChord.m * u t + GConvexChord.C at h
    linarith)
  have jq := cubic_joint
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
  dsimp [alphaModel,gModel]
  norm_num [a,ClassicalSingleBounds.a,ClassicalSingleBounds.s,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma] at j5 j4 jq e1 e2 e3 eh ⊢
  linarith

theorem gModel_upper :
    gModel ≤ GConvexChord.rationalG := by
  change (8/VariableGIntegral.a)*(42823/151875)*log (VariableGIntegral.c 5/VariableGIntegral.a)+8*GConvexChord.endpoint+
    8*(VariableGIntegral.primitive VariableGIntegral.s-VariableGIntegral.primitive (VariableGIntegral.c 4))+8*log (6*VariableGIntegral.a/VariableGIntegral.s) ≤ GConvexChord.rationalG
  rw [VariableGIntegral.endpoint]
  have h1 := log_upper (t := c 5/a)
    (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,a,truncatedSixthLowerAlpha])
  have h2 := log_upper (t := c 4/c 5)
    (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha])
  have h3 := log_upper (t := s/c 4)
    (by norm_num [s,c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h4 := log_upper (t := (4/3 : ℝ)) (by norm_num)
  have h5 := log_upper (t := 6*a/s)
    (by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h6 := log_upper (t := (5/4 : ℝ)) (by norm_num)
  unfold GConvexChord.rationalG GConvexChord.endpoint at *
  norm_num [GConvexChord.m,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,VariableGIntegral.logCoefficient,VariableGIntegral.linearCoefficient,a,truncatedSixthLowerAlpha, c,s,VariableGIntegral.c,VariableGIntegral.s,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerSigma] at h1 h2 h3 h4 h5 h6 ⊢
  linarith


/-- Rational lower payment for the positive part of the JOINT model, not the actual base. -/
def modelBase : ℝ :=
  24*(11104/10125+((11/2)*SharpLogRecurrence.lowerLog (4/3)-(15/4)*(4-3)+
      (4^2-3^2)/2-(4^3-3^3)/36)+GConvexChord.m+GConvexChord.C*SharpLogRecurrence.lowerLog (5/4)+
      (42823/151875)*(1127/200-5))+
  8*(11104/10125+((78/25)^2-3^2)/18-(2/3)*(78/25-3)+2*SharpLogRecurrence.lowerLog ((78/25)/3))

theorem model_base_lower : modelBase ≤ 24*alphaModel+8*wuLowerCoefficient (1/(2*b)) := by
  have hb := BaseRecurrenceLower.beta_real_lower
  have h3 := SharpLogRecurrence.log_three_bounds.1
  have h43 := SharpLogRecurrence.log_lower (by norm_num : (1 : ℝ) ≤ 4/3)
  have h54 := SharpLogRecurrence.log_lower (by norm_num : (1 : ℝ) ≤ 5/4)
  have hb3 := SharpLogRecurrence.log_lower (by norm_num : (1 : ℝ) ≤ (78/25)/3)
  unfold alphaModel modelBase
  rw [CP_difference (by norm_num) (by norm_num),
    BaseRecurrenceLower.P_difference 0 GConvexChord.C GConvexChord.m (by norm_num) (by norm_num)]
  rw [BaseRecurrenceLower.Q_difference (by norm_num) (by norm_num)] at hb
  norm_num [GConvexChord.m,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,
    b,truncatedSixthLowerBeta,SharpLogRecurrence.lowerLog] at hb h43 h54 hb3 ⊢
  linarith

/-- Independently reassembled complete signed lower; the old curvature deduction is NOT added. -/
def kLower : ℝ := modelBase+UnroundedPayments.fifthRational+
    RationalMovingSixth.rationalSixth+SixthReciprocalCorrection.deltaSixth+SixthLogCubicCorrection.deltaLog+47/481250-GConvexChord.rationalG-
    UnroundedPayments.weightedJUpper-FourLogAffine.newFour

theorem complete_lower : kLower < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := model_base_lower
  have hg := shared_actual_lower
  have hm := gModel_upper
  have hj := UnroundedPayments.original_weightedJ_le
  have hi := FourLogAffine.original_four_le_newFour
  have hp := UnroundedPayments.fifthRational_lt_fifthPairFlin
  have hq := SixthLogCubicCorrection.actual_sixth_ge_rational_corrected
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient kLower
  linarith

def deltaK : ℝ := modelBase-BaseRecurrenceLower.newBase-GCurvatureChord.deltaG

theorem improvement_identity : kLower = GCurvatureChord.newBalance+deltaK := by
  unfold kLower GCurvatureChord.newBalance deltaK
  ring

theorem deltaK_pos : 0 < deltaK := by
  norm_num [deltaK,modelBase,BaseRecurrenceLower.newBase,GCurvatureChord.deltaG,
    GConvexChord.m,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,
    VariableGIntegral.a,truncatedSixthLowerAlpha,SharpLogRecurrence.lowerLog]

theorem strict_improvement : GCurvatureChord.newBalance < kLower := by
  rw [improvement_identity]
  linarith only [deltaK_pos]

end
end Wu2008DoubleSieve.Phase23
