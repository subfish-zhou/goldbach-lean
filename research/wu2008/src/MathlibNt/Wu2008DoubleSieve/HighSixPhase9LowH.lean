import MathlibNt.Wu2008DoubleSieve.HighSixPhase9Feedback
import MathlibNt.Wu2008DoubleSieve.SingleUpperHIntegral

namespace Wu2008DoubleSieve.HighSixPhase9
open Real Set MeasureTheory SingleUpperHSource SingleUpperHIntegral
noncomputable section

/-- The endpoint is induced by the second cross, in the original coordinate. -/
def shapeLeft (δ : ℝ) : ℝ := (1/2-δ)-(23/5)*truncatedSixthLowerAlpha

def shapeCoefficient (δ : ℝ) : ℝ := 16*(amplitude δ)*(25/468)/truncatedSixthLowerAlpha^2

def Cgeo : ℝ := 5000211/55203200

theorem shapeCoefficient_nonneg {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    0 ≤ shapeCoefficient δ := by
  unfold shapeCoefficient
  have ha := amplitude_nonneg hδ hδhi
  positivity

theorem Cgeo_pos : 0 < Cgeo := by norm_num [Cgeo]

theorem shape_geometry {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    truncatedSixthLowerAlpha ≤ shapeLeft δ ∧
    shapeLeft δ ≤ (1/2-δ)/2 ∧
    (513/5308 : ℝ) ≤ (1/2-δ)/2-shapeLeft δ := by
  dsimp [shapeLeft,truncatedSixthLowerAlpha]
  constructor
  · linarith
  constructor <;> linarith

/-- The full shape window stays in the proved quadratic argument interval. -/
theorem shape_argument {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc (shapeLeft δ) ((1/2-δ)/2)) :
    argument δ t ∈ Icc (3 : ℝ) (23/5) := by
  constructor
  · apply (le_div_iff₀ (by norm_num [truncatedSixthLowerAlpha])).2
    dsimp [truncatedSixthLowerAlpha]
    linarith [ht.2]
  · apply (div_le_iff₀ (by norm_num [truncatedSixthLowerAlpha])).2
    dsimp [shapeLeft] at ht
    linarith [ht.1]

/-- The kernel comparison retains the square and the original argument. -/
theorem kernel_shape_lower {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc (shapeLeft δ) ((1/2-δ)/2)) :
    shapeCoefficient δ*(t-shapeLeft δ)^2 ≤ kernel δ t := by
  have hg := shape_geometry hδ hδhi
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num [truncatedSixthLowerAlpha])
    (hg.1.trans ht.1)
  have hct : 0 < (1/2-δ)-t := by linarith [ht.2]
  have hd : t*((1/2-δ)-t) ≤ (1/16 : ℝ) := by
    have hc : (1/2-δ)^2 ≤ (1/2 : ℝ)^2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith only [hc,sq_nonneg (t-(1/2-δ)/2)]
  have hH := H_quadratic hδ hδhi (shape_argument hδ hδhi ht)
  have hp : 0 ≤ (amplitude δ)*(25/468)*(23/5-argument δ t)^2 :=
    mul_nonneg (mul_nonneg (amplitude_nonneg hδ hδhi) (by norm_num)) (sq_nonneg _)
  have hk : 16*((amplitude δ)*(25/468)*(23/5-argument δ t)^2) ≤ kernel δ t := by
    unfold kernel
    apply (le_div_iff₀ (mul_pos ht0 hct)).2
    have hh := mul_le_mul_of_nonneg_left hd hp
    nlinarith only [hH,hh]
  have hid : 16*((amplitude δ)*(25/468)*(23/5-argument δ t)^2) =
      shapeCoefficient δ*(t-shapeLeft δ)^2 := by
    unfold argument shapeCoefficient shapeLeft truncatedSixthLowerAlpha
    ring
  rwa [hid] at hk

/-- The comparison integral is evaluated by a genuine cubic primitive. -/
theorem quadratic_integral (a b k : ℝ) :
    (∫ t in a..b, k*(t-a)^2) = k/3*(b-a)^3 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun x : ℝ => (k/3)*(x-a)^3) (k*(t-a)^2) t := by
    intro t
    have hh := (((hasDerivAt_id t).sub (hasDerivAt_const t a)).pow 3).const_mul (k/3)
    convert hh using 1 <;> first | rfl | (norm_num; ring)
  have hi : IntervalIntegrable (fun t : ℝ => k*(t-a)^2) volume a b :=
    (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable a b
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  calc
    _ = (k/3)*(b-a)^3-(k/3)*(a-a)^3 := hf
    _ = _ := by ring

/-- Nonnegativity is established on the entire original integration window. -/
theorem original_window_nonneg {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc truncatedSixthLowerAlpha ((1/2-δ)/2)) : 0 ≤ kernel δ t := by
  have ha : truncatedSixthLowerAlpha/2 ≤ truncatedSixthLowerAlpha := by
    norm_num [truncatedSixthLowerAlpha]
  exact kernel_nonneg hδ hδhi (ha.trans ht.1) ht.2

/-- Both actual subintegrals are integrable before localizing the original window. -/
theorem original_integral_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    shapeCoefficient δ/3*(513/5308)^3 ≤
      ∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), kernel δ t := by
  have hg := shape_geometry hδ hδhi
  have ha : truncatedSixthLowerAlpha/2 ≤ truncatedSixthLowerAlpha := by
    norm_num [truncatedSixthLowerAlpha]
  have hi1 := kernel_integrable hδ hδhi ha hg.1 hg.2.1
  have hi2 := kernel_integrable hδ hδhi (ha.trans hg.1) hg.2.1 le_rfl
  have hfirst : 0 ≤ ∫ t in truncatedSixthLowerAlpha..shapeLeft δ, kernel δ t := by
    apply intervalIntegral.integral_nonneg hg.1
    intro t ht
    exact original_window_nonneg hδ hδhi ⟨ht.1,ht.2.trans hg.2.1⟩
  have hlast : shapeCoefficient δ/3*((1/2-δ)/2-shapeLeft δ)^3 ≤
      ∫ t in shapeLeft δ..((1/2-δ)/2), kernel δ t := by
    have hi : IntervalIntegrable (fun t : ℝ => shapeCoefficient δ*(t-shapeLeft δ)^2)
        volume (shapeLeft δ) ((1/2-δ)/2) :=
      (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on hg.2.1 hi hi2
      (fun t ht => kernel_shape_lower hδ hδhi ht)
    rwa [quadratic_integral] at hm
  have hwidth := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 513/5308) hg.2.2 3)
    (div_nonneg (shapeCoefficient_nonneg hδ hδhi) (by norm_num : (0 : ℝ) ≤ 3))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  linarith only [hfirst,hlast,hwidth,hadd]

/-- The unchanged geometry gives the amplitude coefficient before feedback. -/
theorem Cgeo_identity (δ : ℝ) :
    Cgeo*amplitude δ = 2*(shapeCoefficient δ/3*(513/5308)^3) := by
  unfold Cgeo shapeCoefficient truncatedSixthLowerAlpha
  ring

/-- The two original low windows remain doubled before division by four. -/
theorem actual_low_H_amplitude_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    Cgeo*amplitude δ ≤ gainH34 δ/4 := by
  have hi := original_integral_lower hδ hδhi
  rw [Cgeo_identity]
  dsimp [gainH34,windowGain]
  linarith only [hi]

end
end Wu2008DoubleSieve.HighSixPhase9
