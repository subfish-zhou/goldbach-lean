import FifthShapePayment

namespace Wu2008DoubleSieve.SharedRationalEnvelope
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open FixedCoefficientUpperEnclosure (a s)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u pull)
open scoped Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
noncomputable section

/-- Preserve the original chord density without its polynomial relaxation. -/
theorem density_upper {v : ℝ} (hv : 2 ≤ v) (hv3 : v ≤ 3) :
    wuLowerCoefficient v/v ≤ (v-2)/(2*(v-1)) := by
  have hv0 : 0 < v := by linarith
  have hv1 : v-1 ≠ 0 := by linarith
  have h := VariableUpperEnvelope.log_chord_upper (z := v-2) (by linarith)
  have he0 : wuLowerCoefficient v = log (v-1) :=
    jr1965f_normalized_firstInterval hv (by linarith)
  rw [he0]
  have he : 1+(v-2) = v-1 := by ring
  rw [he] at h
  apply (div_le_iff₀ hv0).2
  convert h using 1 <;> first | rfl | (field_simp [hv1]; ring)

/-- True recurrence and FTC, on the unchanged original interval. -/
theorem upper_log {v : ℝ} (hv : 3 ≤ v) (hv4 : v ≤ 4) :
    wuUpperCoefficient v ≤ 1+(v-3-log (v-2))/2 := by
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 3) hv
  have he : wuUpperCoefficient 3 = 1 := jr1965F_normalized_initial (by norm_num) le_rfl
  have hab : 2 ≤ v-1 := by linarith
  have hi : IntervalIntegrable (fun x : ℝ => (x-2)/(2*(x-1))) volume 2 (v-1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    rw [uIcc_of_le hab] at hx
    have : 0 < 2*(x-1) := by linarith [hx.1]
    exact this.ne'
  have hm := intervalIntegral.integral_mono_on hab
    (wuLowerCoefficient_div_intervalIntegrable (by norm_num) hab) hi
    (fun x hx => density_upper hx.1 (by linarith [hx.2]))
  have hd (x : ℝ) (hx : x ∈ uIcc 2 (v-1)) :
      HasDerivAt (fun x : ℝ => (x-2-log (x-1))/2) ((x-2)/(2*(x-1))) x := by
    rw [uIcc_of_le hab] at hx
    have hn : x-1 ≠ 0 := by linarith [hx.1]
    convert (((hasDerivAt_id x).sub_const 2).sub
      (((hasDerivAt_id x).sub_const 1).log hn)).div_const 2 using 1 <;>
      first | rfl | (dsimp; field_simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi] at hm
  norm_num only [show (3 : ℝ)-1=2 by norm_num,he] at hr
  norm_num at hm
  have hx : v-1-1=v-2 := by ring
  rw [hx] at hm
  linarith

/-- Exactly the previously admitted lowerLog, with no new order or terms. -/
def p (v : ℝ) : ℝ := (v-1-lowerLog (v-2))/2

theorem upper_p {v : ℝ} (hv : 3 ≤ v) (hv4 : v ≤ 4) :
    wuUpperCoefficient v ≤ p v := by
  have h := upper_log hv hv4
  have hl := log_lower (t := v-2) (by linarith)
  unfold p
  linarith

/-- A rational identity for the existing envelopes, not a new approximation. -/
theorem gap_identity {z : ℝ} (hz : 0 ≤ z) :
    VariableUpperEnvelope.cubic (z+3)-p (z+3) =
      z^3*(8-3*z^2-z^3)/(12*(z+2)^3) := by
  have hn : z+2 ≠ 0 := by linarith
  unfold VariableUpperEnvelope.cubic p lowerLog
  have he : z+3-2+1=z+2 := by ring
  rw [he]
  field_simp
  ring

/-- Lower payment from the same cubic factor, not a higher-order envelope. -/
theorem gap_lower {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    z^3/81 ≤ VariableUpperEnvelope.cubic (z+3)-p (z+3) := by
  rw [gap_identity hz]
  have hz2 : z^2 ≤ 1 := by nlinarith
  have hz3 : z^3 ≤ 1 := by nlinarith [mul_nonneg hz (sub_nonneg.mpr hz2)]
  have hden : (z+2)^3 ≤ 27 := by nlinarith
  have hn : 4 ≤ 8-3*z^2-z^3 := by linarith
  have hd : 0 < 12*(z+2)^3 := by positivity
  apply (le_div_iff₀ hd).2
  nlinarith [mul_nonneg (pow_nonneg hz 3) (sub_nonneg.mpr hn),
    mul_nonneg (pow_nonneg hz 3) (sub_nonneg.mpr hden)]

theorem window_order : a ≤ c 4 ∧ c 4 ≤ s ∧ s < 1/3 := by
  norm_num [a,c,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]

theorem geometry {t : ℝ} (ht : t ∈ Icc (c 4) s) :
    0 < t ∧ 0 < 1/2-t ∧ 3 ≤ u t ∧ u t ≤ 4 := by
  have ha := truncatedSixthLower_parameters.1
  have ht0 := ha.trans_le (window_order.1.trans ht.1)
  have hd : 0 < 1/2-t := by linarith [ht.2,window_order.2.2]
  refine ⟨ht0,hd,?_,?_⟩
  · apply (le_div_iff₀ ha).2
    have h : t ≤ 1/2-3*a := ht.2
    linarith
  · apply (div_le_iff₀ ha).2
    have h : 1/2-4*a ≤ t := ht.1
    linarith

def weight (t : ℝ) : ℝ := (8-24*t)/(t*(1/2-t))
def gainDensity (t : ℝ) : ℝ := weight t*(VariableUpperEnvelope.cubic (u t)-p (u t))
def deltaShared : ℝ := ∫ t in c 4..s, gainDensity t
def fixedGain : ℝ := 4*a*(8-24*s)/81

theorem p_continuous : ContinuousOn (fun t => p (u t)) (Icc (c 4) s) := by
  unfold p lowerLog
  apply ContinuousOn.div_const
  apply ContinuousOn.sub
  · unfold u; fun_prop
  · apply ContinuousOn.add
    · apply ContinuousOn.const_mul
      apply ContinuousOn.div (by unfold u; fun_prop) (by unfold u; fun_prop)
      intro t ht
      linarith [(geometry ht).2.2.1]
    · apply ContinuousOn.div_const
      apply ContinuousOn.const_mul
      apply ContinuousOn.pow
      apply ContinuousOn.div (by unfold u; fun_prop) (by unfold u; fun_prop)
      intro t ht
      linarith [(geometry ht).2.2.1]

theorem density_continuous : ContinuousOn gainDensity (Icc (c 4) s) := by
  apply ContinuousOn.mul
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact mul_ne_zero (geometry ht).1.ne' (geometry ht).2.1.ne'
  · exact (by unfold VariableUpperEnvelope.cubic u; fun_prop :
      ContinuousOn (fun t => VariableUpperEnvelope.cubic (u t)) (Icc (c 4) s)).sub p_continuous

theorem density_lower {t : ℝ} (ht : t ∈ Icc (c 4) s) :
    (16*(8-24*s)/81)*(u t-3)^3 ≤ gainDensity t := by
  obtain ⟨ht0,hd,hu3,hu4⟩ := geometry ht
  have hgap := gap_lower (z := u t-3) (by linarith) (by linarith)
  rw [sub_add_cancel] at hgap
  have hs : 0 < 8-24*s := by linarith [window_order.2.2]
  have hden : t*(1/2-t) ≤ 1/16 := by nlinarith [sq_nonneg (t-1/4)]
  have hw : 16*(8-24*s) ≤ weight t := by
    apply (le_div_iff₀ (mul_pos ht0 hd)).2
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hden),ht.2]
  have hp : 0 ≤ (u t-3)^3/81 := by positivity
  have hh := mul_le_mul hw hgap hp (by linarith : 0 ≤ weight t)
  unfold gainDensity
  nlinarith only [hh]

/-- Positive fixed rational payment, integrated by the true cubic primitive. -/
theorem fixedGain_le_delta : fixedGain ≤ deltaShared := by
  have hi : IntervalIntegrable gainDensity volume (c 4) s :=
    density_continuous.intervalIntegrable_of_Icc window_order.2.1
  have hc : Continuous (fun t => (16*(8-24*s)/81)*(u t-3)^3) := by unfold u; fun_prop
  have hm := intervalIntegral.integral_mono_on window_order.2.1
    (hc.intervalIntegrable _ _) hi (fun t ht => density_lower ht)
  have hd (t : ℝ) (_ht : t ∈ uIcc (c 4) s) :
      HasDerivAt (fun t => -(16*(8-24*s)/81)*a/4*(u t-3)^4)
        ((16*(8-24*s)/81)*(u t-3)^3) t := by
    have ha := truncatedSixthLower_parameters.1.ne'
    convert (((((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).div_const a).sub_const 3).pow 4 |>.const_mul (-(16*(8-24*s)/81)*a/4)) using 1 <;>
      first | rfl | (dsimp [u]; field_simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)] at hm
  have h4 : u (c 4)=4 := by norm_num [u,a,c,truncatedSixthLowerAlpha]
  have h3 : u s=3 := by norm_num [u,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  rw [h4,h3] at hm
  norm_num at hm
  dsimp [fixedGain,deltaShared]
  linarith

theorem fixedGain_pos : 0 < fixedGain := by
  unfold fixedGain
  have ha := truncatedSixthLower_parameters.1
  have hs : 0 < 8-24*s := by linarith [window_order.2.2]
  positivity

theorem deltaShared_pos : 0 < deltaShared := fixedGain_pos.trans_le fixedGain_le_delta

/-- The negative joint weight is used before either alpha or G is bounded. -/
theorem cubic_joint_gain :
    24*(Phase23.CP 4-Phase23.CP 3)-
      8*(VariableGIntegral.primitive s-VariableGIntegral.primitive (c 4))+deltaShared ≤
      24*(pull s-pull (c 4))-8*(∫ t in c 4..s, ClassicalSingleBounds.g t) := by
  let m := fun t => VariableUpperEnvelope.cubic (u t)/(t*(1/2-t))
  have hg := ClassicalSingleBounds.g_integrable window_order.1 window_order.2.2.le window_order.2.1
  have htg : IntervalIntegrable (fun t => t*ClassicalSingleBounds.g t) volume (c 4) s :=
    hg.continuousOn_mul continuousOn_id
  have hm : IntervalIntegrable m volume (c 4) s := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by dsimp [m,VariableUpperEnvelope.cubic,u]; fun_prop) (by fun_prop)
    intro t ht
    rw [uIcc_of_le window_order.2.1] at ht
    exact mul_ne_zero (geometry ht).1.ne' (geometry ht).2.1.ne'
  have htm : IntervalIntegrable (fun t => t*m t) volume (c 4) s :=
    hm.continuousOn_mul continuousOn_id
  have hd : IntervalIntegrable gainDensity volume (c 4) s :=
    density_continuous.intervalIntegrable_of_Icc window_order.2.1
  have hbound := intervalIntegral.integral_mono_on window_order.2.1
    (((htm.const_mul 24).sub (hm.const_mul 8)).add hd)
    ((htg.const_mul 24).sub (hg.const_mul 8)) (fun t ht => by
      obtain ⟨ht0,hdt,hu3,hu4⟩ := geometry ht
      have hn : 24*t-8 ≤ 0 := by linarith [ht.2,window_order.2.2]
      have hh := mul_le_mul_of_nonpos_left
        (div_le_div_of_nonneg_right (upper_p hu3 hu4) (mul_pos ht0 hdt).le) hn
      change _ ≤ (24*t-8)*ClassicalSingleBounds.g t at hh
      dsimp [m,gainDensity,weight]
      convert hh using 1 <;> ring)
  have eg : (∫ t in c 4..s, t*ClassicalSingleBounds.g t) = pull s-pull (c 4) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ htg
    intro t ht
    rw [uIcc_of_le window_order.2.1] at ht
    exact Phase22.pull_derivative ⟨window_order.1.trans ht.1,ht.2⟩
  have eH : (∫ t in c 4..s, m t) = VariableGIntegral.primitive s-VariableGIntegral.primitive (c 4) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hm
    intro t ht
    rw [uIcc_of_le window_order.2.1] at ht
    exact VariableGIntegral.derivative (geometry ht).1.ne' (by linarith [(geometry ht).2.1])
  have eP : (∫ t in c 4..s, t*m t) = Phase23.CP 4-Phase23.CP 3 := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => -Phase23.CP (u t)) (fun t ht => ?_) htm
    · have h4 : u (c 4)=4 := by norm_num [u,a,c,truncatedSixthLowerAlpha]
      have h3 : u s=3 := by norm_num [u,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
      rw [h4,h3] at he
      linarith
    rw [uIcc_of_le window_order.2.1] at ht
    have hu : u t ≠ 0 := by linarith [(geometry ht).2.2.1]
    convert ((Phase23.CP_derivative hu).comp t
      (((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).div_const a)).neg using 1
    · rfl
    · dsimp [m,u]
      field_simp [truncatedSixthLower_parameters.1.ne',(geometry ht).1.ne',
        (geometry ht).2.1.ne']
      ring
  rw [intervalIntegral.integral_add ((htm.const_mul 24).sub (hm.const_mul 8)) hd,
    intervalIntegral.integral_sub (htm.const_mul 24) (hm.const_mul 8),
    intervalIntegral.integral_sub (htg.const_mul 24) (hg.const_mul 8),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,eP,eH,eg] at hbound
  exact hbound

end
end Wu2008DoubleSieve.SharedRationalEnvelope
