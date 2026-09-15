import SecondCrossShapes

namespace Wu2008DoubleSieve.Phase11
open Real Set MeasureTheory HighSixPhase9 SingleUpperHSource SingleUpperHIntegral
noncomputable section

/-- Fixed endpoints induced by the fourth envelope and the original delta bound. -/
def a0 : ℝ := 1/2-(33/5)*truncatedSixthLowerAlpha
def b0 : ℝ := 49/100-5*truncatedSixthLowerAlpha
def tailCoefficient (δ : ℝ) : ℝ := 16*amplitude δ*k4/truncatedSixthLowerAlpha^4
def Ctail : ℝ := 2*(16*k4/truncatedSixthLowerAlpha^4)*
  ((b0-a0)^5-(truncatedSixthLowerAlpha-a0)^5)/5
def Ctotal : ℝ := Cgeo+Ctail

theorem fixed_endpoints : a0 = (7/2654 : ℝ) ∧ b0 = (15023/132700 : ℝ) ∧
    b0-truncatedSixthLowerAlpha = (5023/132700 : ℝ) := by
  norm_num [a0,b0,truncatedSixthLowerAlpha]

theorem Ctail_exact : Ctail =
    (596451289474909364593/1199841552000000000000000 : ℝ) := by
  norm_num [Ctail,k4,a0,b0,truncatedSixthLowerAlpha]

theorem Ctail_pos : 0 < Ctail := by rw [Ctail_exact]; norm_num

theorem Ctotal_pos : 0 < Ctotal := add_pos Cgeo_pos Ctail_pos

theorem tail_geometry {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    a0 < truncatedSixthLowerAlpha ∧ truncatedSixthLowerAlpha < b0 ∧
    b0 < shapeLeft δ ∧ shapeLeft δ ≤ (1/2-δ)/2 := by
  have hg := shape_geometry hδ hδhi
  refine ⟨by norm_num [a0,truncatedSixthLowerAlpha],
    by norm_num [b0,truncatedSixthLowerAlpha], ?_, hg.2.1⟩
  dsimp [b0,shapeLeft,truncatedSixthLowerAlpha]
  linarith

/-- This window lies wholly in the new quartic argument domain. -/
theorem tail_argument {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc truncatedSixthLowerAlpha b0) :
    argument δ t ∈ Icc (5 : ℝ) (33/5) := by
  constructor
  · apply (le_div_iff₀ (by norm_num [truncatedSixthLowerAlpha])).2
    dsimp [b0] at ht
    linarith [ht.2]
  · apply (div_le_iff₀ (by norm_num [truncatedSixthLowerAlpha])).2
    dsimp [truncatedSixthLowerAlpha] at *
    linarith [ht.1]

/-- The quartic stays in the actual prime-coordinate kernel, with the original weight. -/
theorem kernel_tail_lower {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc truncatedSixthLowerAlpha b0) :
    tailCoefficient δ*(t-a0)^4 ≤ kernel δ t := by
  have hg := tail_geometry hδ hδhi
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num [truncatedSixthLowerAlpha]) ht.1
  have htHi : t ≤ (1/2-δ)/2 := ht.2.trans (hg.2.2.1.le.trans hg.2.2.2)
  have hct : 0 < (1/2-δ)-t := by linarith
  have hd : t*((1/2-δ)-t) ≤ (1/16 : ℝ) := by
    have hc : (1/2-δ)^2 ≤ (1/2 : ℝ)^2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith only [hc,sq_nonneg (t-(1/2-δ)/2)]
  have hH := H_quartic hδ hδhi (tail_argument hδ hδhi ht)
  have hp : 0 ≤ amplitude δ*k4*(33/5-argument δ t)^4 :=
    mul_nonneg (mul_nonneg (amplitude_nonneg hδ hδhi) (by norm_num [k4]))
      (pow_nonneg (by linarith [(tail_argument hδ hδhi ht).2]) _)
  have hk : 16*(amplitude δ*k4*(33/5-argument δ t)^4) ≤ kernel δ t := by
    unfold kernel
    apply (le_div_iff₀ (mul_pos ht0 hct)).2
    have hh := mul_le_mul_of_nonneg_left hd hp
    nlinarith only [hH,hh]
  have hid : 16*(amplitude δ*k4*(33/5-argument δ t)^4) =
      tailCoefficient δ*(t-((1/2-δ)-(33/5)*truncatedSixthLowerAlpha))^4 := by
    unfold argument tailCoefficient truncatedSixthLowerAlpha
    ring
  rw [hid] at hk
  have hc0 : 0 ≤ tailCoefficient δ := by
    unfold tailCoefficient k4
    have ha := amplitude_nonneg hδ hδhi
    positivity
  have hpow : (t-a0)^4 ≤ (t-((1/2-δ)-(33/5)*truncatedSixthLowerAlpha))^4 := by
    apply pow_le_pow_left₀ (by linarith [hg.1,ht.1])
    dsimp [a0]
    linarith
  exact (mul_le_mul_of_nonneg_left hpow hc0).trans hk

/-- A genuine fifth-degree FTC on the fixed new tail. -/
theorem quartic_integral (a b d k : ℝ) :
    (∫ t in a..b, k*(t-d)^4) = k/5*((b-d)^5-(a-d)^5) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun x : ℝ => (k/5)*(x-d)^5) (k*(t-d)^4) t := by
    intro t
    have hh := (((hasDerivAt_id t).sub (hasDerivAt_const t d)).pow 5).const_mul (k/5)
    convert hh using 1 <;> first | rfl | (norm_num; ring)
  have hi : IntervalIntegrable (fun t : ℝ => k*(t-d)^4) volume a b :=
    (continuous_const.mul ((continuous_id.sub continuous_const).pow 4)).intervalIntegrable a b
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  calc
    _ = (k/5)*(b-d)^5-(k/5)*(a-d)^5 := hf
    _ = _ := by ring

/-- Reassemble ONE integral at two disjoint cutpoints. No old whole-window lower is added. -/
theorem disjoint_original_integral_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    tailCoefficient δ/5*((b0-a0)^5-(truncatedSixthLowerAlpha-a0)^5)+
      shapeCoefficient δ/3*(513/5308)^3 ≤
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
  have hmiddle : 0 ≤ ∫ t in b0..shapeLeft δ, kernel δ t := by
    apply intervalIntegral.integral_nonneg hg.2.2.1.le
    intro t ht
    exact original_window_nonneg hδ hδhi ⟨hg.2.1.le.trans ht.1,ht.2.trans hg.2.2.2⟩
  have hlast : shapeCoefficient δ/3*((1/2-δ)/2-shapeLeft δ)^3 ≤
      ∫ t in shapeLeft δ..((1/2-δ)/2), kernel δ t := by
    have hi : IntervalIntegrable (fun t : ℝ => shapeCoefficient δ*(t-shapeLeft δ)^2)
        volume (shapeLeft δ) ((1/2-δ)/2) :=
      (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on hg.2.2.2 hi hi3
      (fun t ht => kernel_shape_lower hδ hδhi ht)
    rwa [quadratic_integral] at hm
  have hwidth := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 513/5308) hs.2.2 3)
    (div_nonneg (shapeCoefficient_nonneg hδ hδhi) (by norm_num : (0 : ℝ) ≤ 3))
  have hadd12 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hadd123 := intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3
  linarith only [htail,hmiddle,hlast,hwidth,hadd12,hadd123]

theorem Ctail_identity (δ : ℝ) :
    Ctail*amplitude δ = 2*(tailCoefficient δ/5*
      ((b0-a0)^5-(truncatedSixthLowerAlpha-a0)^5)) := by
  unfold Ctail tailCoefficient
  ring

/-- Preserve the two original low windows and their final division by four. -/
theorem actual_low_H_total_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    Ctotal*amplitude δ ≤ gainH34 δ/4 := by
  have hi := disjoint_original_integral_lower hδ hδhi
  rw [Ctotal,add_mul,Cgeo_identity,Ctail_identity]
  dsimp [gainH34,windowGain]
  linarith only [hi]

end
end Wu2008DoubleSieve.Phase11
