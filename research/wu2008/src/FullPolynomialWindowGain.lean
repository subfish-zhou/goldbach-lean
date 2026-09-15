import RetainedEndpointShapes

namespace Wu2008DoubleSieve.Phase14
open Real Set MeasureTheory HighSixPhase9 SingleUpperHSource SingleUpperHIntegral Phase11 Phase12
open Phase13 (κh κH κh_pos κH_pos H_retained_quadratic)
noncomputable section

def w0 : ℝ := 513/5308
def width (δ : ℝ) : ℝ := (1/2-δ)/2-shapeLeft δ
def q1 : ℝ := κh*5/(18*truncatedSixthLowerAlpha)
def q2 : ℝ := 25/(468*truncatedSixthLowerAlpha^2)
def poly (x : ℝ) : ℝ := κH+q1*x+q2*x^2
def primitive (x : ℝ) : ℝ := κH*x+q1/2*x^2+q2/3*x^3
def deltaC : ℝ := 32*(κH*w0+q1/2*w0^2)
def C14 : ℝ := Cfull+deltaC

theorem width_identity (δ : ℝ) : width δ = w0+δ/2 := by
  unfold width w0 shapeLeft truncatedSixthLowerAlpha
  ring

theorem width_lower {δ : ℝ} (hδ : 0 < δ) : w0 ≤ width δ := by
  rw [width_identity]
  linarith

theorem q1_pos : 0 < q1 := by norm_num [q1,κh,truncatedSixthLowerAlpha]
theorem q2_pos : 0 < q2 := by norm_num [q2,truncatedSixthLowerAlpha]
theorem deltaC_exact : deltaC = (13072/1068235 : ℝ) := by
  norm_num [deltaC,w0,q1,κH,κh,truncatedSixthLowerAlpha]
theorem deltaC_pos : 0 < deltaC := by rw [deltaC_exact]; norm_num
theorem C14_pos : 0 < C14 := add_pos Cfull_pos deltaC_pos

theorem poly_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ poly x :=
  add_nonneg (add_nonneg κH_pos.le (mul_nonneg q1_pos.le hx))
    (mul_nonneg q2_pos.le (sq_nonneg x))

/-- A single full polynomial envelope, with the original positive denominator. -/
theorem kernel_full_polynomial_lower {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc (shapeLeft δ) ((1/2-δ)/2)) :
    16*amplitude δ*poly (t-shapeLeft δ) ≤ kernel δ t := by
  have hg := shape_geometry hδ hδhi
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num [truncatedSixthLowerAlpha])
    (hg.1.trans ht.1)
  have hct : 0 < (1/2-δ)-t := by linarith [ht.2]
  have hd : t*((1/2-δ)-t) ≤ (1/16 : ℝ) := by
    have hc : (1/2-δ)^2 ≤ (1/2 : ℝ)^2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith only [hc,sq_nonneg (t-(1/2-δ)/2)]
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
  have hh := mul_le_mul_of_nonneg_left hd hp
  nlinarith only [hH,hh]

theorem polynomial_integrable (a b k : ℝ) :
    IntervalIntegrable (fun t : ℝ => k*poly (t-a)) volume a b := by
  exact (continuous_const.mul ((continuous_const.add
    (continuous_const.mul (continuous_id.sub continuous_const))).add
    (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)))).intervalIntegrable _ _

/-- A genuine cubic primitive evaluates the one full comparison integral. -/
theorem polynomial_integral (a b k : ℝ) :
    (∫ t in a..b, k*poly (t-a)) = k*primitive (b-a) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun x : ℝ => k*primitive (x-a)) (k*poly (t-a)) t := by
    intro t
    have h := (hasDerivAt_id t).sub (hasDerivAt_const t a)
    have hh := ((h.const_mul κH).add ((h.pow 2).const_mul (q1/2))).add
      ((h.pow 3).const_mul (q2/3))
    have hk := hh.const_mul k
    convert hk using 1 <;> first | rfl | (dsimp [poly]; ring)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (polynomial_integrable a b k)
  calc
    _ = k*primitive (b-a)-k*primitive (a-a) := hf
    _ = _ := by simp [primitive]

/-- The upper endpoint remains the moving c(delta)/2. -/
theorem full_polynomial_integral_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    16*amplitude δ*primitive (width δ) ≤
      ∫ t in shapeLeft δ..((1/2-δ)/2), kernel δ t := by
  have hg := shape_geometry hδ hδhi
  have ha : truncatedSixthLowerAlpha/2 ≤ truncatedSixthLowerAlpha := by
    norm_num [truncatedSixthLowerAlpha]
  have hi := kernel_integrable hδ hδhi (ha.trans hg.1) hg.2.1 le_rfl
  have hm := intervalIntegral.integral_mono_on hg.2.1
    (polynomial_integrable (shapeLeft δ) ((1/2-δ)/2) (16*amplitude δ)) hi
    (fun t ht => kernel_full_polynomial_lower hδ hδhi ht)
  rwa [polynomial_integral] at hm

theorem primitive_width_lower {δ : ℝ} (hδ : 0 < δ) :
    primitive w0 ≤ primitive (width δ) := by
  have hw := width_lower hδ
  have h0 : (0 : ℝ) ≤ w0 := by norm_num [w0]
  have h1 := mul_le_mul_of_nonneg_left hw κH_pos.le
  have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hw 2)
    (div_nonneg q1_pos.le (by norm_num : (0 : ℝ) ≤ 2))
  have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hw 3)
    (div_nonneg q2_pos.le (by norm_num : (0 : ℝ) ≤ 3))
  exact add_le_add (add_le_add h1 h2) h3

theorem fixed_polynomial_integral_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    16*amplitude δ*primitive w0 ≤
      ∫ t in shapeLeft δ..((1/2-δ)/2), kernel δ t :=
  (mul_le_mul_of_nonneg_left (primitive_width_lower hδ)
    (mul_nonneg (by norm_num) (amplitude_nonneg hδ hδhi))).trans
    (full_polynomial_integral_lower hδ hδhi)

/-- Rebuild tail, middle and the new full polynomial on ONE original integral. -/
theorem three_piece_full_polynomial_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    tailCoefficient δ/5*((b0-a0)^5-(truncatedSixthLowerAlpha-a0)^5)+
      16*amplitude δ*primitive w0+
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
  have hlast := fixed_polynomial_integral_lower hδ hδhi
  have hadd12 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hadd123 := intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3
  linarith only [htail,hmiddle,hlast,hadd12,hadd123]

theorem polynomial_coefficient_identity (δ : ℝ) :
    (Cgeo+deltaC)*amplitude δ = 2*(16*amplitude δ*primitive w0) := by
  rw [add_mul,Cgeo_identity]
  unfold deltaC primitive q2 shapeCoefficient w0
  ring

/-- Genuine original two-window doubling, followed by the original division by four. -/
theorem actual_low_H_polynomial_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    C14*amplitude δ ≤ gainH34 δ/4 := by
  have hi := three_piece_full_polynomial_lower hδ hδhi
  have he : C14*amplitude δ = (Cgeo+deltaC)*amplitude δ+
      Ctail*amplitude δ+Cmid*amplitude δ := by unfold C14 Cfull; ring
  rw [he,polynomial_coefficient_identity,Ctail_identity,Cmid_identity]
  dsimp [gainH34,windowGain]
  linarith only [hi]

end
end Wu2008DoubleSieve.Phase14
