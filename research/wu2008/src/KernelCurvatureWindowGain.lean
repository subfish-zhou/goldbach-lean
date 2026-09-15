import FullPolynomialWindowGain

namespace Wu2008DoubleSieve.Phase15
open Real Set MeasureTheory HighSixPhase9 SingleUpperHSource SingleUpperHIntegral Phase11 Phase12
open Phase13 (κh κH κh_pos κH_pos H_retained_quadratic)
open Phase14 (w0 width q1 q2 poly primitive q1_pos q2_pos poly_nonneg width_lower)
noncomputable section

/-- The fixed curvature remainder is not an optimized or scanned parameter. -/
def curvatureMass (w : ℝ) : ℝ := κH*w^3/3+q1*w^4/12+q2*w^5/30
def fullMass (w : ℝ) : ℝ := 16*primitive w+256*curvatureMass w
def deltaKernel : ℝ := 512*curvatureMass w0
def C15 : ℝ := Phase14.C14+deltaKernel

/-- A quintic primitive of the complete quartic, with moving width held as a parameter. -/
def curvaturePrimitive (w x : ℝ) : ℝ :=
  16*primitive x+256*(κH*(w^2*x-w*x^2+x^3/3)+
    q1*(w^2*x^2/2-2*w*x^3/3+x^4/4)+
    q2*(w^2*x^3/3-w*x^4/2+x^5/5))

theorem deltaKernel_exact : deltaKernel = (273217240947699/156506354394208000 : ℝ) := by
  norm_num [deltaKernel,curvatureMass,w0,q1,q2,κH,κh,truncatedSixthLowerAlpha]
theorem deltaKernel_pos : 0 < deltaKernel := by rw [deltaKernel_exact]; norm_num
theorem C15_pos : 0 < C15 := add_pos Phase14.C14_pos deltaKernel_pos

/-- Uniform quadratic improvement for the original positive kernel denominator. -/
theorem multiplier_denominator {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    (16+256*((1/2-δ)/2-t)^2)*(t*((1/2-δ)-t)) ≤ 1 := by
  have hc : (1/2-δ)^2 ≤ (1/2 : ℝ)^2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hd : t*((1/2-δ)-t) ≤ 1/16-((1/2-δ)/2-t)^2 := by
    nlinarith only [hc]
  have hm : 0 ≤ 16+256*((1/2-δ)/2-t)^2 := by positivity
  have hh := mul_le_mul_of_nonneg_left hd hm
  have he : (16+256*((1/2-δ)/2-t)^2)*(1/16-((1/2-δ)/2-t)^2) =
      1-256*((1/2-δ)/2-t)^4 := by ring
  rw [he] at hh
  nlinarith only [hh, sq_nonneg (((1/2-δ)/2-t)^2)]

/-- One simultaneous envelope: no addition of independent lower bounds. -/
theorem kernel_curvature_polynomial_lower {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc (shapeLeft δ) ((1/2-δ)/2)) :
    amplitude δ*poly (t-shapeLeft δ)*(16+256*((1/2-δ)/2-t)^2) ≤ kernel δ t := by
  have hg := shape_geometry hδ hδhi
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num [truncatedSixthLowerAlpha])
    (hg.1.trans ht.1)
  have hct : 0 < (1/2-δ)-t := by linarith [ht.2]
  have hH := H_retained_quadratic hδ hδhi (shape_argument hδ hδhi ht)
  have he : amplitude δ*(κH+(25/468)*(23/5-argument δ t)^2+
      κh*(5/18)*(23/5-argument δ t)) = amplitude δ*poly (t-shapeLeft δ) := by
    unfold poly q1 q2 argument shapeLeft truncatedSixthLowerAlpha
    ring
  rw [he] at hH
  have hp := mul_nonneg (amplitude_nonneg hδ hδhi)
    (poly_nonneg (sub_nonneg.mpr ht.1))
  unfold kernel
  apply (le_div_iff₀ (mul_pos ht0 hct)).2
  have hh := mul_le_mul_of_nonneg_left (multiplier_denominator hδ hδhi (t := t)) hp
  calc
    _ = amplitude δ*poly (t-shapeLeft δ)*
        ((16+256*((1/2-δ)/2-t)^2)*(t*((1/2-δ)-t))) := by ring
    _ ≤ amplitude δ*poly (t-shapeLeft δ)*1 := hh
    _ ≤ _ := by simpa only [mul_one] using hH

theorem curvature_polynomial_integrable (a b k : ℝ) :
    IntervalIntegrable (fun t : ℝ => k*poly (t-a)*(16+256*(b-t)^2)) volume a b := by
  apply Continuous.intervalIntegrable
  unfold poly
  fun_prop

/-- Real FTC applied to the entire quartic integrand, not a correction added to an old bound. -/
theorem curvature_polynomial_integral (a b k : ℝ) :
    (∫ t in a..b, k*poly (t-a)*(16+256*(b-t)^2)) = k*fullMass (b-a) := by
  let w := b-a
  have hd : ∀ t : ℝ, HasDerivAt (fun x : ℝ => k*curvaturePrimitive w (x-a))
      (k*poly (t-a)*(16+256*(b-t)^2)) t := by
    intro t
    have h := (hasDerivAt_id t).sub (hasDerivAt_const t a)
    have h3 := ((h.const_mul κH).add ((h.pow 2).const_mul (q1/2))).add
      ((h.pow 3).const_mul (q2/3))
    have hc := ((((h.const_mul (w^2)).sub ((h.pow 2).const_mul w)).add
      ((h.pow 3).div_const 3)).const_mul κH)
    have hl := (((((h.pow 2).const_mul (w^2)).div_const 2).sub
      (((h.pow 3).const_mul (2*w)).div_const 3)).add
      ((h.pow 4).div_const 4)).const_mul q1
    have hq := (((((h.pow 3).const_mul (w^2)).div_const 3).sub
      (((h.pow 4).const_mul w).div_const 2)).add
      ((h.pow 5).div_const 5)).const_mul q2
    have hk := ((h3.const_mul 16).add (((hc.add hl).add hq).const_mul 256)).const_mul k
    convert hk using 1 <;> first | rfl | (dsimp [curvaturePrimitive,primitive,poly,w]; ring)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (curvature_polynomial_integrable a b k)
  calc
    _ = k*curvaturePrimitive w (b-a)-k*curvaturePrimitive w (a-a) := hf
    _ = _ := by dsimp [w,curvaturePrimitive,fullMass,curvatureMass,primitive]; ring

theorem full_curvature_integral_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    amplitude δ*fullMass (width δ) ≤
      ∫ t in shapeLeft δ..((1/2-δ)/2), kernel δ t := by
  have hg := shape_geometry hδ hδhi
  have ha : truncatedSixthLowerAlpha/2 ≤ truncatedSixthLowerAlpha := by
    norm_num [truncatedSixthLowerAlpha]
  have hi := kernel_integrable hδ hδhi (ha.trans hg.1) hg.2.1 le_rfl
  have hm := intervalIntegral.integral_mono_on hg.2.1
    (curvature_polynomial_integrable (shapeLeft δ) ((1/2-δ)/2) (amplitude δ)) hi
    (fun t ht => kernel_curvature_polynomial_lower hδ hδhi ht)
  rwa [curvature_polynomial_integral] at hm

theorem fullMass_width_lower {δ : ℝ} (hδ : 0 < δ) :
    fullMass w0 ≤ fullMass (width δ) := by
  have hw := width_lower hδ
  have h0 : (0 : ℝ) ≤ w0 := by norm_num [w0]
  have h1 := Phase14.primitive_width_lower hδ
  have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hw 3) κH_pos.le
  have h4 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hw 4) q1_pos.le
  have h5 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hw 5) q2_pos.le
  dsimp [fullMass,curvatureMass]
  linarith only [h1,h3,h4,h5]

theorem fixed_curvature_integral_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    amplitude δ*fullMass w0 ≤
      ∫ t in shapeLeft δ..((1/2-δ)/2), kernel δ t :=
  (mul_le_mul_of_nonneg_left (fullMass_width_lower hδ) (amplitude_nonneg hδ hδhi)).trans
    (full_curvature_integral_lower hδ hδhi)

/-- Reassemble the same original integral from its tail, middle, and curvature-polynomial pieces. -/
theorem three_piece_curvature_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    tailCoefficient δ/5*((b0-a0)^5-(truncatedSixthLowerAlpha-a0)^5)+
      amplitude δ*fullMass w0+
      (16*amplitude δ*middleMass)*((2/5)*truncatedSixthLowerAlpha) ≤
      ∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), kernel δ t := by
  have hg := tail_geometry hδ hδhi
  have hs := shape_geometry hδ hδhi
  have ha : truncatedSixthLowerAlpha/2 ≤ truncatedSixthLowerAlpha := by
    norm_num [truncatedSixthLowerAlpha]
  have hi1 := kernel_integrable hδ hδhi ha hg.2.1.le (hg.2.2.1.le.trans hg.2.2.2)
  have hi2 := kernel_integrable hδ hδhi (ha.trans hg.2.1.le) hg.2.2.1.le hg.2.2.2
  have hi3 := kernel_integrable hδ hδhi (ha.trans hs.1) hg.2.2.2 le_rfl
  have htail : tailCoefficient δ/5*((b0-a0)^5-(truncatedSixthLowerAlpha-a0)^5) ≤
      ∫ t in truncatedSixthLowerAlpha..b0, kernel δ t := by
    have hi : IntervalIntegrable (fun t : ℝ => tailCoefficient δ*(t-a0)^4)
        volume truncatedSixthLowerAlpha b0 :=
      (continuous_const.mul ((continuous_id.sub continuous_const).pow 4)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on hg.2.1.le hi hi1
      (fun t ht => kernel_tail_lower hδ hδhi ht)
    rwa [quartic_integral] at hm
  have hmiddle := middle_integral_lower hδ hδhi
  have hlast := fixed_curvature_integral_lower hδ hδhi
  have hadd12 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hadd123 := intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3
  linarith only [htail,hmiddle,hlast,hadd12,hadd123]

theorem curvature_coefficient_identity (δ : ℝ) :
    (Cgeo+Phase14.deltaC+deltaKernel)*amplitude δ = 2*(amplitude δ*fullMass w0) := by
  rw [add_mul,Phase14.polynomial_coefficient_identity]
  unfold deltaKernel fullMass
  ring

/-- Original two-window symmetry and division by four, now with the restored curvature. -/
theorem actual_low_H_curvature_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    C15*amplitude δ ≤ gainH34 δ/4 := by
  have hi := three_piece_curvature_lower hδ hδhi
  have he : C15*amplitude δ = (Cgeo+Phase14.deltaC+deltaKernel)*amplitude δ+
      Ctail*amplitude δ+Cmid*amplitude δ := by unfold C15 Phase14.C14 Cfull; ring
  rw [he,curvature_coefficient_identity,Ctail_identity,Cmid_identity]
  dsimp [gainH34,windowGain]
  linarith only [hi]

end
end Wu2008DoubleSieve.Phase15
