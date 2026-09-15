import MathlibNt.Wu2008DoubleSieve.BaseUpperSplitCoefficient
import MathlibNt.Wu2008DoubleSieve.GCurvatureCount

namespace Wu2008DoubleSieve.Phase22
open Real Set MeasureTheory ClassicalAnalyticLeaves
open FixedCoefficientUpperEnclosure (a b s reciprocalPrimitive)
open FixedCoefficientHLowerEnclosure (c)
open scoped Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
noncomputable section

def u (t : ℝ) : ℝ := (1/2-t)/a
def pull (t : ℝ) : ℝ := -wuLowerCoefficient (u t+1)

theorem pull_derivative {t : ℝ} (ht : t ∈ Icc a s) :
    HasDerivAt pull (t*ClassicalSingleBounds.g t) t := by
  have ha := truncatedSixthLower_parameters.1
  have ht0 := ha.trans_le ht.1
  have hu : 3 ≤ u t := by
    apply (le_div_iff₀ ha).2
    have hs : t ≤ 1/2-3*a := ht.2
    linarith
  have hz : u t ≠ 0 := by linarith
  have hd : 1/2-t ≠ 0 := by
    have hs : t ≤ 1/2-3*a := ht.2
    linarith
  have hf := (hasDerivAt_mul_jr1965f (show 2 < u t+1 by linarith)).div_const
    (2*exp eulerMascheroniConstant)
  have hf' : HasDerivAt wuLowerCoefficient (wuUpperCoefficient (u t)/(u t)) (u t+1) := by
    convert! hf using 1
    rw [show u t+1-1=u t by ring,wuUpperCoefficient_div hz]
  have hc := hf'.comp t (((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).div_const a |>.add_const 1)
  apply hc.neg.congr_deriv
  dsimp [ClassicalSingleBounds.g,u]
  field_simp [ha.ne',ht0.ne',hd]
  ring

/-- The full signed multiplier is nonpositive on every original low-G segment.
This is where the shared actual delay coefficient is cancelled BEFORE bounding. -/
theorem joint_segment (p P H : ℝ → ℝ) {l r : ℝ}
    (hl : a ≤ l) (hr : r ≤ s) (hlr : l ≤ r)
    (hp : Continuous p)
    (hP : ∀ v, 0 < v → HasDerivAt P (p v/v) v)
    (hH : ∀ t ∈ Icc l r, HasDerivAt H (p (u t)/(t*(1/2-t))) t)
    (hbound : ∀ t ∈ Icc l r, p (u t) ≤ wuUpperCoefficient (u t)) :
    24*(pull r-pull l)-8*(∫ t in l..r, ClassicalSingleBounds.g t) ≤
      24*(P (u l)-P (u r))-8*(H r-H l) := by
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
    ((htgi.const_mul 24).sub (hg.const_mul 8))
    ((htm.const_mul 24).sub (hm.const_mul 8)) (fun t ht => by
      have h := div_le_div_of_nonneg_right (hbound t ht)
        (mul_pos (geom t ht).1 (geom t ht).2.1).le
      have hn : 24*t-8 ≤ 0 := by linarith [ht.2.trans hr3]
      have hh := mul_le_mul_of_nonpos_left h hn
      change (24*t-8)*ClassicalSingleBounds.g t ≤ _ at hh
      nlinarith only [hh])
  have ep : (∫ t in l..r, t*ClassicalSingleBounds.g t) = pull r-pull l := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ htgi
    intro t ht
    rw [uIcc_of_le hlr] at ht
    exact pull_derivative ⟨hl.trans ht.1,ht.2.trans hr⟩
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

def AP (j C d t : ℝ) : ℝ := C*reciprocalPrimitive t+d*GVariableIntegral.affinePrimitive j t
def QP (t : ℝ) : ℝ := reciprocalPrimitive t+GVariableQuadratic.quadraticPrimitive t

theorem affine_joint (j C d : ℝ) {l r : ℝ}
    (hl : a ≤ l) (hr : r ≤ s) (hlr : l ≤ r)
    (hb : ∀ t ∈ Icc l r, C+d*(u t-j) ≤ wuUpperCoefficient (u t)) :
    24*(pull r-pull l)-8*(∫ t in l..r, ClassicalSingleBounds.g t) ≤
      24*(BaseRecurrenceLower.P j C d (u l)-BaseRecurrenceLower.P j C d (u r))-
      8*(AP j C d r-AP j C d l) := by
  apply joint_segment (fun v => C+d*(v-j)) (BaseRecurrenceLower.P j C d) (AP j C d)
    hl hr hlr (by fun_prop) (fun v hv => BaseRecurrenceLower.P_derivative j C d hv.ne') _ hb
  intro t ht
  have ht0 := truncatedSixthLower_parameters.1.trans_le (hl.trans ht.1)
  have ht1 : t < 1/2 := by linarith [ht.2.trans (hr.trans truncatedSixthLower_parameters.2.2.2.1.le)]
  convert! ((GVariableIntegral.reciprocal_derivative ht0 ht1).const_mul C).add
    ((GVariableIntegral.affine_derivative (j := j) ht0 ht1).const_mul d) using 1
  dsimp [u]
  ring

theorem quadratic_joint :
    24*(pull s-pull (c 4))-8*(∫ t in c 4..s, ClassicalSingleBounds.g t) ≤
      24*(BaseRecurrenceLower.Q 4-BaseRecurrenceLower.Q 3)-8*(QP s-QP (c 4)) := by
  have hl : a ≤ c 4 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have hlr : c 4 ≤ s := by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hu4 : u (c 4) = 4 := by norm_num [u,a,c,truncatedSixthLowerAlpha]
  have hu3 : u s = 3 := by norm_num [u,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  suffices h : 24*(pull s-pull (c 4))-8*(∫ t in c 4..s, ClassicalSingleBounds.g t) ≤
      24*(BaseRecurrenceLower.Q (u (c 4))-BaseRecurrenceLower.Q (u s))-8*(QP s-QP (c 4)) by
    simpa only [hu4,hu3] using h
  apply joint_segment (fun v => 1+(v-3)^2/9) BaseRecurrenceLower.Q QP
    hl le_rfl hlr (by fun_prop) (fun v hv => BaseRecurrenceLower.Q_derivative hv.ne')
  · intro t ht
    have ht0 := truncatedSixthLower_parameters.1.trans_le (hl.trans ht.1)
    have ht1 : t < 1/2 := by linarith [ht.2, truncatedSixthLower_parameters.2.2.2.1]
    convert! (GVariableIntegral.reciprocal_derivative ht0 ht1).add
      (GVariableQuadratic.quadratic_derivative ht0 ht1) using 1
    dsimp [u]
    ring
  · intro t ht
    have h3 : 3 ≤ u t := by
      apply (le_div_iff₀ truncatedSixthLower_parameters.1).2
      have h : t ≤ 1/2-3*a := ht.2
      linarith
    have h4 : u t ≤ 4 := by
      apply (div_le_iff₀ truncatedSixthLower_parameters.1).2
      have h : 1/2-4*a ≤ t := ht.1
      linarith
    exact SharpSingleBalance.upper_quadratic h3 h4

def alphaModel : ℝ := log 3+(BaseRecurrenceLower.Q 4-BaseRecurrenceLower.Q 3)+
  (BaseRecurrenceLower.P 4 (34832/30375) (56/243) 5-BaseRecurrenceLower.P 4 (34832/30375) (56/243) 4)+
  (BaseRecurrenceLower.P 5 (340/243) (2776/10125) (1127/200)-BaseRecurrenceLower.P 5 (340/243) (2776/10125) 5)

/-- Unconditional shared-base/G upper; alphaModel is NOT an upper bound for the actual base. -/
theorem shared_actual_upper :
    24*wuLowerCoefficient (1/(2*a))-
      (SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s) ≤
    24*alphaModel-(FixedCoefficientHLowerEnclosure.Hbound+GVariableCoefficient.exactGain) := by
  have h5 : a ≤ c 5 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have h54 : c 5 ≤ c 4 := by norm_num [a,c,truncatedSixthLowerAlpha]
  have h4s : c 4 ≤ s := by norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hs3 := truncatedSixthLower_parameters.2.2.2.1.le
  have j5 := affine_joint 5 (340/243) (2776/10125) le_rfl (h54.trans h4s) h5 (fun t ht => by
    apply GVariableRecurrence.upper_five_affine
    apply (le_div_iff₀ truncatedSixthLower_parameters.1).2
    have hh : t ≤ 1/2-5*a := ht.2
    linarith)
  have j4 := affine_joint 4 (34832/30375) (56/243) h5 h4s h54 (fun t ht => by
    apply GVariableRecurrence.upper_four_affine
    apply (le_div_iff₀ truncatedSixthLower_parameters.1).2
    have hh : t ≤ 1/2-4*a := ht.2
    linarith)
  have jq := quadratic_joint
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
  dsimp [alphaModel,AP,QP,FixedCoefficientHLowerEnclosure.Hbound,GVariableCoefficient.exactGain] at j5 j4 jq ⊢
  linarith

/-- This rational belongs to the JOINT envelope, never to the actual positive base alone. -/
def sharedBaseCap : ℝ := 58604765335652/1092191900625

theorem model_plus_beta_upper :
    24*alphaModel+8*wuLowerCoefficient (1/(2*b)) ≤ sharedBaseCap := by
  have hb := FixedCoefficientScalarEnclosure.lower_affine_upper
    (s := 1/(2*b)) (by norm_num [b,truncatedSixthLowerBeta])
  have hl3 := SharpLogRecurrence.log_three_bounds.2
  have h43 := SharpLogRecurrence.log_upper (by norm_num : (1 : ℝ) ≤ 4/3)
  have h54 := SharpLogRecurrence.log_upper (by norm_num : (1 : ℝ) ≤ 5/4)
  have hT := SharpLogRecurrence.log_upper (by norm_num : (1 : ℝ) ≤ (1127/200)/5)
  unfold alphaModel
  rw [BaseRecurrenceLower.Q_difference (by norm_num) (by norm_num),
    BaseRecurrenceLower.P_difference 4 (34832/30375) (56/243) (by norm_num) (by norm_num),
    BaseRecurrenceLower.P_difference 5 (340/243) (2776/10125) (by norm_num) (by norm_num)]
  norm_num [SharpLogRecurrence.upperLog,sharedBaseCap,b,truncatedSixthLowerBeta] at hb h43 h54 hT ⊢
  linarith

def newUpper : ℝ := BaseUpperSplitCoefficient.newUpper-
  (BaseUpperSplitRecurrence.newBase-sharedBaseCap)

theorem complete_upper : TruncatedElevenClassicalCountLower.classicalCoefficient ≤ newUpper := by
  have hjoint := shared_actual_upper
  have hb := model_plus_beta_upper
  have hg := add_le_add FixedCoefficientHLowerEnclosure.rationalH_lower
    GVariableCoefficient.rational_gain_lower
  have hf := RetainedSixthCoefficient.actual_fifth_upper
  have hs := NaturalSplitActual.actual_sixth_upper
  have hj := JCubicRationalLower.weighted_J_lower
  have hi := FourPositiveRationalLower.actual_weighted_lower
  unfold newUpper BaseUpperSplitCoefficient.newUpper
    TruncatedElevenClassicalCountLower.classicalCoefficient
  unfold FourPositiveRationalLower.weightedRational at hi ⊢
  linarith

theorem gain_exact : BaseUpperSplitCoefficient.newUpper-newUpper =
    (27501906098537/54609595031250 : ℝ) := by
  norm_num [newUpper,sharedBaseCap,BaseUpperSplitRecurrence.newBase,a,b,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem improvement_more_than_half : newUpper+1/2 < BaseUpperSplitCoefficient.newUpper := by
  linarith only [gain_exact]

theorem new_upper_lt_nine_halves : newUpper < (9/2 : ℝ) := by
  unfold newUpper
  rw [BaseUpperSplitCoefficient.envelope_identity,BaseUpperSplitRecurrence.base_difference]
  norm_num [NaturalSplitCoefficient.exactUpper,FourPositiveExactEnvelope.exactUpper,
    NaturalSplitActual.exactGain,BaseUpperSplitRecurrence.newBase,sharedBaseCap,
    a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem actual_lt_nine_halves : TruncatedElevenClassicalCountLower.classicalCoefficient < (9/2 : ℝ) :=
  complete_upper.trans_lt new_upper_lt_nine_halves

end
end Wu2008DoubleSieve.Phase22
