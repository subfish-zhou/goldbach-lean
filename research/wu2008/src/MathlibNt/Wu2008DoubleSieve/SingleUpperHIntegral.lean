import MathlibNt.Wu2008DoubleSieve.SingleUpperHPacking
import MathlibNt.Wu2008DoubleSieve.SingleUpperLowEndpoint

namespace Wu2008DoubleSieve.SingleUpperHIntegral
open Set Real MeasureTheory SingleUpperHSource SingleUpperQuadrature
open scoped Classical Topology

/-- Effective monotonicity is available beyond s=3; H-antitonicity is not used. -/
theorem effective_argument_antitone {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    AntitoneOn (fun t => effective δ (argument δ t))
      (Icc (truncatedSixthLowerAlpha/2) ((1/2-δ)/2)) := by
  intro x hx y hy hxy
  have hs := argument_bounds hδ hδhi hy.1 hy.2
  have ht := argument_bounds hδ hδhi hx.1 hx.2
  have harg : argument δ y ≤ argument δ x := by
    apply div_le_div_of_nonneg_right (by linarith) (by norm_num [truncatedSixthLowerAlpha])
  exact wu_effective_upper_limit_mono hδ (by linarith) hs.1 harg ht.2

/-- The whole original low interval is outside the imported positive seed domain. -/
theorem low_argument_gt_three {δ t : ℝ} (hδhi : δ ≤ 1/100)
    (ht : t ≤ (1/2-δ)/2) : 3 < argument δ t := by
  apply (lt_div_iff₀ (by norm_num [truncatedSixthLowerAlpha])).mpr
  norm_num [truncatedSixthLowerAlpha] at *
  linarith

noncomputable def kernel (δ t : ℝ) : ℝ :=
  wuImprovementLimit true δ (argument δ t) / (t*((1/2-δ)-t))

noncomputable def effectiveKernel (δ t : ℝ) : ℝ :=
  effective δ (argument δ t) / (t*((1/2-δ)-t))

/-- The denominator keeps the original prime coordinate, not s in its place. -/
theorem reciprocal_continuous {δ a b : ℝ} (_hδhi : δ ≤ 1/100)
    (ha : truncatedSixthLowerAlpha/2 ≤ a) (hab : a ≤ b) (hb : b ≤ (1/2-δ)/2) :
    ContinuousOn (fun t => (t*((1/2-δ)-t))⁻¹) (uIcc a b) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num [truncatedSixthLowerAlpha]) (ha.trans ht.1)
  have hd0 : 0 < (1/2-δ)-t := by linarith [ht.2]
  exact (mul_pos ht0 hd0).ne'

theorem effective_integrable {δ a b : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ha : truncatedSixthLowerAlpha/2 ≤ a) (hab : a ≤ b) (hb : b ≤ (1/2-δ)/2) :
    IntervalIntegrable (effectiveKernel δ) volume a b := by
  have hm : AntitoneOn (fun t => effective δ (argument δ t)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (effective_argument_antitone hδ hδhi).mono
      (fun _ ht => ⟨ha.trans ht.1,ht.2.trans hb⟩)
  change IntervalIntegrable (fun t => effective δ (argument δ t) / (t*((1/2-δ)-t))) volume a b
  simpa only [div_eq_mul_inv] using
    (hm.intervalIntegrable (μ := volume)).mul_continuousOn
      (reciprocal_continuous hδhi ha hab hb)

/-- Integrability is obtained as continuous A minus monotone effective A-H.
No pointwise regularity or delta continuity of H is a premise. -/
theorem kernel_integrable {δ a b : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ha : truncatedSixthLowerAlpha/2 ≤ a) (hab : a ≤ b) (hb : b ≤ (1/2-δ)/2) :
    IntervalIntegrable (kernel δ) volume a b := by
  have hc : ContinuousOn (fun t => wuUpperCoefficient (argument δ t)) (uIcc a b) := by
    apply continuousOn_wuUpperCoefficient.comp (by unfold argument; fun_prop)
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hs := argument_bounds hδ hδhi (ha.trans ht.1) (ht.2.trans hb)
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs.1
  have hi := hc.intervalIntegrable (μ := volume)
  have hw := hi.mul_continuousOn (reciprocal_continuous hδhi ha hab hb)
  have he := effective_integrable hδ hδhi ha hab hb
  convert hw.sub he using 1
  ext t
  dsimp [kernel,effectiveKernel,effective]
  ring

theorem kernel_nonneg {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : truncatedSixthLowerAlpha/2 ≤ t) (htHi : t ≤ (1/2-δ)/2) :
    0 ≤ kernel δ t := by
  have hs := argument_bounds hδ hδhi ht htHi
  have hH := wuImprovementLimit_nonneg true hδ (by linarith) hs.1 hs.2
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num [truncatedSixthLowerAlpha]) ht
  have hd0 : 0 < (1/2-δ)-t := by linarith
  exact div_nonneg hH (mul_pos ht0 hd0).le

/-- Algebraic normalization separates the H saving before taking any bounds. -/
theorem kernel_split (δ t : ℝ) :
    effectiveKernel δ t = weight δ t/t - kernel δ t := by
  dsimp [effectiveKernel,effective,kernel,weight,argument]
  simp only [sub_div,div_div,mul_comm]

/-- Each original window has its own factor four, as in packing_exact. -/
noncomputable def windowGain (δ : ℝ) : ℝ :=
  4 * ∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), kernel δ t

noncomputable def gainH34 (δ : ℝ) : ℝ := windowGain δ + windowGain δ

theorem gainH34_eq (δ : ℝ) : gainH34 δ =
    8 * ∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2),
      wuImprovementLimit true δ (((1/2-δ)-t)/truncatedSixthLowerAlpha) /
        (t*((1/2-δ)-t)) := by
  dsimp [gainH34,windowGain,kernel,argument]
  ring

theorem windowGain_nonneg {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    0 ≤ windowGain δ := by
  have hab : truncatedSixthLowerAlpha ≤ (1/2-δ)/2 := by
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hi : 0 ≤ ∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), kernel δ t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact kernel_nonneg hδ hδhi
      ((by norm_num [truncatedSixthLowerAlpha] : truncatedSixthLowerAlpha/2 ≤ truncatedSixthLowerAlpha).trans ht.1) ht.2
  exact mul_nonneg (by norm_num) hi

theorem gainH34_nonneg {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    0 ≤ gainH34 δ := add_nonneg (windowGain_nonneg hδ hδhi) (windowGain_nonneg hδ hδhi)

/-- This is the exact integral identity, not a count estimate. -/
theorem low_integral_split {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    4 * (∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), effectiveKernel δ t) =
      4 * (∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), weight δ t/t) - windowGain δ := by
  have hab : truncatedSixthLowerAlpha ≤ (1/2-δ)/2 := by
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hi := SingleUpperLowEndpoint.density_integrable hδ.le hδhi
    (by norm_num [truncatedSixthLowerAlpha] : (1/15 : ℝ) ≤ truncatedSixthLowerAlpha)
    hab (by linarith : (1/2-δ)/2 ≤ 1/3)
  have hh := kernel_integrable hδ hδhi
    (by norm_num [truncatedSixthLowerAlpha] : truncatedSixthLowerAlpha/2 ≤ truncatedSixthLowerAlpha) hab le_rfl
  simp_rw [kernel_split]
  rw [intervalIntegral.integral_sub hi hh]
  dsimp [windowGain]
  ring

end Wu2008DoubleSieve.SingleUpperHIntegral
