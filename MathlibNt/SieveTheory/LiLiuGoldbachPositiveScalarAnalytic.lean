import MathlibNt.SieveTheory.LiLiuGoldbachPositiveScalarPolynomial
open Set MeasureTheory Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
set_option maxRecDepth 10000
set_option maxHeartbeats 0

noncomputable def goldbachPositiveScalarK (z : ℝ) : ℝ := 1/(1-z)-1/(3-z)

/-- Exact signed remainder: the subtracted geometric tail has the correct sign. -/
theorem goldbachPositiveScalarH_remainder {z : ℝ} (_hz : 0 ≤ z) (hzu : z ≤ 1/2) :
    goldbachPositiveScalarK z - goldbachPositiveScalarH z =
      z^32/(1-z) - (z/3)^32/(3-z) := by
  have h1 : 1-z ≠ 0 := by linarith
  have h3 : 3-z ≠ 0 := by linarith
  have hG : (∑ k ∈ range 32, z^k) = (1-z^32)/(1-z) :=
    (eq_div_iff h1).2 (geom_sum_mul_neg z 32)
  have hJ : (1/3 : ℝ)*(∑ k ∈ range 32, (z/3)^k) =
      (1-(z/3)^32)/(3-z) := by
    apply (eq_div_iff h3).2
    calc
      _ = (∑ k ∈ range 32, (z/3)^k) * (1-z/3) := by ring
      _ = _ := geom_sum_mul_neg (z/3) 32
  rw [goldbachPositiveScalarH_eq, hG, hJ]
  unfold goldbachPositiveScalarK
  ring

/-- Fixed whole-interval geometric error, not a finite-point test. -/
theorem goldbachPositiveScalarH_bounds {z : ℝ} (hz : 0 ≤ z) (hzu : z ≤ 1/2) :
    0 ≤ goldbachPositiveScalarK z - goldbachPositiveScalarH z ∧
    goldbachPositiveScalarK z - goldbachPositiveScalarH z ≤ 1/2^31 := by
  rw [goldbachPositiveScalarH_remainder hz hzu]
  have h1 : 0 < 1-z := by linarith
  have h3 : 0 < 3-z := by linarith
  have hp : (z/3)^32/(3-z) ≤ z^32/(1-z) := by
    gcongr <;> linarith
  constructor
  · exact sub_nonneg.mpr hp
  · calc
      _ ≤ z^32/(1-z) := sub_le_self _ (by positivity)
      _ ≤ (1/2 : ℝ)^32/(1/2) := by gcongr; linarith
      _ = _ := by norm_num

/-- Bounds on the exact Jacobian kernel. -/
theorem goldbachPositiveScalarK_bounds {z : ℝ} (_hz : 0 ≤ z) (hzu : z ≤ 1/2) :
    0 ≤ goldbachPositiveScalarK z ∧ goldbachPositiveScalarK z ≤ 2 := by
  have h1 : 0 < 1-z := by linarith
  have h3 : 0 < 3-z := by linarith
  unfold goldbachPositiveScalarK
  constructor
  · apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le h1 (by linarith)
  · calc
      _ ≤ 1/(1-z) := sub_le_self _ (by positivity)
      _ ≤ 2 := (div_le_iff₀ h1).2 (by linarith)

/-- Pointwise derivative comparison on every real point of the actual v-window. -/
theorem goldbachPositiveScalar_derivative_bounds {v : ℝ} (hv : v ∈ Icc (3 : ℝ) 5) :
    let z := (v-3)/(v-1)
    0 ≤ jurkatRichertInnerIntegral v/v -
      (goldbachPositiveScalarP z*goldbachPositiveScalarH z)*(2/(v-1)^2) ∧
    jurkatRichertInnerIntegral v/v -
      (goldbachPositiveScalarP z*goldbachPositiveScalarH z)*(2/(v-1)^2) ≤ 1/10^8 := by
  let z := (v-3)/(v-1)
  have h1 : 0 < v-1 := by linarith [hv.1]
  have hz : 0 ≤ z := div_nonneg (by linarith [hv.1]) h1.le
  have hzu : z ≤ 1/2 := (div_le_iff₀ h1).2 (by linarith [hv.2])
  have hvfull : v ∈ Icc (3 : ℝ) (45/8) := ⟨hv.1, by linarith [hv.2]⟩
  have hP := goldbachS3_innerPolynomial_le_inner hvfull
  rw [← goldbachPositiveScalarP_eq] at hP
  have hI := goldbachS3_inner_le_envelope hvfull
  unfold goldbachS3_innerEnvelope at hI
  rw [← goldbachPositiveScalarP_eq] at hI
  change jurkatRichertInnerIntegral v ≤ goldbachPositiveScalarP z + z/10^9 at hI
  have hP0 := goldbachPositiveScalarP_nonneg hz
  have hPu : goldbachPositiveScalarP z ≤ 1 := by
    have hi := goldbachS3_inner_quadratic_majorant hv.1
    have hv3 : 0 ≤ v-3 := by linarith [hv.1]
    have hvs : (v-3)^2 ≤ 4 := by nlinarith [hv.2]
    linarith
  obtain ⟨hK0, hKu⟩ := goldbachPositiveScalarK_bounds hz hzu
  obtain ⟨hH0, hHu⟩ := goldbachPositiveScalarH_bounds hz hzu
  have hJ0 : 0 ≤ 2/(v-1)^2 := by positivity
  have hJu : 2/(v-1)^2 ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos h1)).2
    nlinarith [hv.1]
  have he : goldbachPositiveScalarK z * (2/(v-1)^2) = 1/v :=
    (goldbachPositiveScalar_change v hv.1).2.2.2
  have hid : jurkatRichertInnerIntegral v/v -
      (goldbachPositiveScalarP z*goldbachPositiveScalarH z)*(2/(v-1)^2) =
      ((jurkatRichertInnerIntegral v-goldbachPositiveScalarP z)*goldbachPositiveScalarK z +
       goldbachPositiveScalarP z*(goldbachPositiveScalarK z-goldbachPositiveScalarH z)) *
        (2/(v-1)^2) := by
    have he' : jurkatRichertInnerIntegral v/v =
        jurkatRichertInnerIntegral v*goldbachPositiveScalarK z*(2/(v-1)^2) := by
      rw [mul_assoc, he]
      ring
    rw [he']
    ring
  change 0 ≤ _ ∧ _ ≤ _
  rw [hid]
  have hgap0 : 0 ≤ jurkatRichertInnerIntegral v-goldbachPositiveScalarP z := sub_nonneg.mpr hP
  have hgapu : jurkatRichertInnerIntegral v-goldbachPositiveScalarP z ≤ (1/2 : ℝ)/10^9 := by
    linarith
  constructor
  · positivity
  · calc
      _ ≤ (((1/2 : ℝ)/10^9)*2+1*(1/2^31))*(1/2) := by gcongr
      _ ≤ (1 : ℝ)/10^8 := by norm_num

/-- FTC derivative of the polynomial in the original variable. -/
theorem goldbachPositiveScalarA_comp_hasDerivAt {v : ℝ} (hv : 3 ≤ v) :
    HasDerivAt (fun v : ℝ => goldbachPositiveScalarA ((v-3)/(v-1)))
      ((goldbachPositiveScalarP ((v-3)/(v-1))*goldbachPositiveScalarH ((v-3)/(v-1)))*
        (2/(v-1)^2)) v := by
  have hz : HasDerivAt (fun v : ℝ => (v-3)/(v-1)) (2/(v-1)^2) v := by
    apply (((hasDerivAt_id v).sub_const 3).div
      ((hasDerivAt_id v).sub_const 1) (show v-1 ≠ 0 by linarith)).congr_deriv
    dsimp
    ring
  exact (goldbachPositiveScalarA_hasDerivAt _).comp v hz

/-- Integral sandwich for the literal existing lower-factor correction. -/
theorem goldbachPositiveScalar_integral_bounds {b : ℝ} (hb : b ∈ Icc (3 : ℝ) 5) :
    goldbachPositiveScalarA ((b-3)/(b-1)) ≤
      (∫ v in (3 : ℝ)..b, jurkatRichertInnerIntegral v/v) ∧
    (∫ v in (3 : ℝ)..b, jurkatRichertInnerIntegral v/v) ≤
      goldbachPositiveScalarA ((b-3)/(b-1)) + (b-3)/10^8 := by
  let g : ℝ → ℝ := fun v =>
    (goldbachPositiveScalarP ((v-3)/(v-1))*goldbachPositiveScalarH ((v-3)/(v-1)))*
      (2/(v-1)^2)
  have hf : IntervalIntegrable (fun v : ℝ => jurkatRichertInnerIntegral v/v) volume 3 b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hb.1]
    exact (goldbachS3_inner_continuousOn hb.1).div continuousOn_id
      (fun v hv => by dsimp; linarith [hv.1])
  have hP : Continuous goldbachPositiveScalarP := by unfold goldbachPositiveScalarP; fun_prop
  have hH : Continuous goldbachPositiveScalarH := by unfold goldbachPositiveScalarH; fun_prop
  have hz : ContinuousOn (fun v : ℝ => (v-3)/(v-1)) (Icc 3 b) :=
    (continuousOn_id.sub continuousOn_const).div (continuousOn_id.sub continuousOn_const)
      (fun v hv => by dsimp; linarith [hv.1])
  have hg : IntervalIntegrable g volume 3 b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hb.1]
    exact ((hP.comp_continuousOn hz).mul (hH.comp_continuousOn hz)).mul
      (continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
        (fun v hv => pow_ne_zero _ (by dsimp; linarith [hv.1])))
  have he : (∫ v in (3 : ℝ)..b, g v) = goldbachPositiveScalarA ((b-3)/(b-1)) := by
    have hd : ∀ v ∈ uIcc (3 : ℝ) b,
        HasDerivAt (fun v : ℝ => goldbachPositiveScalarA ((v-3)/(v-1))) (g v) v := by
      intro v hv
      rw [uIcc_of_le hb.1] at hv
      exact goldbachPositiveScalarA_comp_hasDerivAt hv.1
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hg
    simpa only [sub_self, zero_div, goldbachPositiveScalarA_zero, sub_zero] using h
  constructor
  · rw [← he]
    apply intervalIntegral.integral_mono_on hb.1 hg hf
    intro v hv
    have h := (goldbachPositiveScalar_derivative_bounds ⟨hv.1, hv.2.trans hb.2⟩).1
    exact sub_nonneg.mp h
  · have hle : (∫ v in (3 : ℝ)..b, jurkatRichertInnerIntegral v/v) ≤
        ∫ v in (3 : ℝ)..b, g v + 1/10^8 := by
      apply intervalIntegral.integral_mono_on hb.1 hf (hg.add (intervalIntegrable_const))
      intro v hv
      have h := (goldbachPositiveScalar_derivative_bounds ⟨hv.1, hv.2.trans hb.2⟩).2
      change _ - g v ≤ _ at h
      linarith
    rw [intervalIntegral.integral_add hg intervalIntegrable_const, he] at hle
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one_div] using hle

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig