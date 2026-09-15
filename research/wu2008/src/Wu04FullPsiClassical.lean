import Wu04CoupledCostProducer
import MathlibNt.Wu2008DoubleSieve.ClassicalLogBounds

namespace Wu04FullPsiClassical
open Wu2008DoubleSieve Set MeasureTheory Real
noncomputable section

/-- Integrated existing reciprocal-tangent bound, not a new Taylor approximation. -/
def jPrimitive (A t : ℝ) : ℝ :=
  (2-4/A)*(log t-log (1-t)) + 4/(A*t)
def jDensity (A t : ℝ) : ℝ := 2*(A*t-2)/(A*t^2*(1-t))
def jLower (B A : ℝ) : ℝ :=
  jPrimitive A (1-1/A) - jPrimitive A (1-1/B)

theorem jPrimitive_deriv {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (jPrimitive A) (jDensity A t) t := by
  have h1 : 1-t ≠ 0 := by linarith
  have h := (((hasDerivAt_log ht.ne').sub
    (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).log h1)).const_mul (2-4/A)).add
    ((hasDerivAt_const t (4:ℝ)).div ((hasDerivAt_id t).const_mul A) (mul_ne_zero hA.ne' ht.ne'))
  convert h using 1 <;> first | rfl | (dsimp [jPrimitive, jDensity]; field_simp; ring)

theorem jDensity_continuous {A a b : ℝ} (hA : 0 < A) (ha : 0 < a) (hb : b < 1) :
    ContinuousOn (jDensity A) (Icc a b) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro t ht
  exact mul_ne_zero (mul_ne_zero hA.ne' (pow_ne_zero _ (ha.trans_le ht.1).ne'))
    (by linarith [ht.2])

theorem j_lower {A B : ℝ} (hB : 2 < B) (hBA : B ≤ A)
    (hg : 2 ≤ A*(1-1/B)) : jLower B A ≤ fourthRowClassicalJ B A := by
  have hA : 0 < A := (show (0:ℝ) < B by linarith).trans_le hBA
  have hab : 1-1/B ≤ 1-1/A := sub_le_sub_left
    (one_div_le_one_div_of_le (by linarith) hBA) 1
  have ha : 0 < 1-1/B := by
    have h := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) (by linarith : (1:ℝ)<B)
    exact sub_pos.mpr (by simpa only [one_div_one] using h)
  have hb : 1-1/A < 1 := sub_lt_self 1 (one_div_pos.mpr hA)
  have hc := jDensity_continuous hA ha hb
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) (by linarith)
  have he : (∫ t in (1-1/B)..(1-1/A), jDensity A t) = jLower B A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hab] at ht
      exact jPrimitive_deriv hA (ha.trans_le ht.1) (ht.2.trans_lt hb)
    · exact hi
  rw [← he]
  apply intervalIntegral.integral_mono_on hab hi (fourthRowClassical_J_integrable hBA hB)
  intro t ht
  have ht0 := ha.trans_le ht.1
  have ht1 : 0 < 1-t := by linarith [ht.2]
  have hz : 1 ≤ A*t-1 := by nlinarith [mul_le_mul_of_nonneg_left ht.1 hA.le]
  have hl := ClassicalLogBounds.log_tangent_lower (a:=1) (b:=A*t-1) (by norm_num) hz
  simp only [log_one, sub_zero] at hl
  have hd := div_le_div_of_nonneg_right hl (mul_nonneg ht0.le ht1.le)
  convert hd using 1 <;> first | rfl | (dsimp [jDensity]; field_simp; ring)

/-- Upper bound for the positive-oriented L terms at S and kappa1. -/
def lUpper (A : ℝ) : ℝ := (A-3-log (A-2))/2

theorem l_upper {A : ℝ} (hA : 3 ≤ A) : fourthRowClassicalL A ≤ lUpper A := by
  have hp (t : ℝ) (ht : t ∈ Icc 2 (A-1)) : 0 < t ∧ 0 < t-1 := by
    constructor <;> linarith [ht.1]
  have hc : ContinuousOn (fun t : ℝ => (t-2)/(2*(t-1))) (Icc 2 (A-1)) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact mul_ne_zero (by norm_num) (hp t ht).2.ne'
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) (by linarith)
  have he : (∫ t in (2:ℝ)..(A-1), (t-2)/(2*(t-1))) = lUpper A := by
    have h : (∫ t in (2:ℝ)..(A-1), (t-2)/(2*(t-1))) =
        ((A-1)-log ((A-1)-1))/2 - (2-log (2-1))/2 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => (t-log (t-1))/2)
      · intro t ht
        rw [uIcc_of_le (by linarith : (2:ℝ)≤A-1)] at ht
        convert ((hasDerivAt_id t).sub (((hasDerivAt_id t).sub_const 1).log (hp t ht).2.ne')).div_const 2 using 1 <;> first | rfl | (dsimp; field_simp [(hp t ht).2.ne']; ring)
      · exact hi
    rw [h]
    norm_num only [lUpper, show (2:ℝ)-1=1 by norm_num, log_one]
    rw [show A-1-1=A-2 by ring]
    ring
  rw [← he]
  apply intervalIntegral.integral_mono_on (by linarith) (fourthRowClassical_L_integrable (by linarith)) hi
  intro t ht
  have hl := SecondFunctionalFourSevenths.log_chord_bound (a:=1) (b:=t-1)
    (by norm_num) (by linarith [ht.1])
  simp only [div_one] at hl
  have hd := div_le_div_of_nonneg_right hl (hp t ht).1.le
  convert hd using 1 <;> first | rfl | (field_simp [(hp t ht).1.ne', (hp t ht).2.ne']; ring)

/-- Correct orientation when kappa2 is below 3: no negative interval is dropped. -/
def lSmallUpper (A : ℝ) : ℝ := 2*log ((A-1)/2)-log (A-2)

theorem l_small_upper {A : ℝ} (hA : 2 < A) (hA3 : A ≤ 3) :
    fourthRowClassicalL A ≤ lSmallUpper A := by
  have hab : A-1 ≤ 2 := by linarith
  have hp (t : ℝ) (ht : t ∈ Icc (A-1) 2) : 0 < t ∧ 0 < t-1 := by
    constructor <;> linarith [ht.1]
  have hc : ContinuousOn (fun t : ℝ => (1-1/(t-1))/t) (Icc (A-1) 2) := by
    apply ContinuousOn.div
    · exact continuousOn_const.sub (continuousOn_const.div
        (continuousOn_id.sub continuousOn_const) (fun t ht => (hp t ht).2.ne'))
    · exact continuousOn_id
    · exact fun t ht => (hp t ht).1.ne'
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) (by linarith)
  have he : (∫ t in (A-1)..(2:ℝ), (1-1/(t-1))/t) = -lSmallUpper A := by
    have h : (∫ t in (A-1)..(2:ℝ), (1-1/(t-1))/t) =
        (2*log 2-log (2-1)) - (2*log (A-1)-log ((A-1)-1)) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => 2*log t-log (t-1))
      · intro t ht
        rw [uIcc_of_le hab] at ht
        convert ((hasDerivAt_log (hp t ht).1.ne').const_mul 2).sub
          (((hasDerivAt_id t).sub_const 1).log (hp t ht).2.ne') using 1 <;> first | rfl | (dsimp; field_simp [(hp t ht).1.ne', (hp t ht).2.ne']; ring)
      · exact hi
    rw [h]
    rw [lSmallUpper, log_div (by linarith : A-1 ≠ 0) (by norm_num : (2:ℝ)≠0)]
    norm_num only [show (2:ℝ)-1=1 by norm_num, log_one]
    rw [show A-1-1=A-2 by ring]
    ring
  have hl : (∫ t in (A-1)..(2:ℝ), (1-1/(t-1))/t) ≤
      ∫ t in (A-1)..(2:ℝ), log (t-1)/t := by
    apply intervalIntegral.integral_mono_on hab hi (fourthRowClassical_L_integrable hA).symm
    intro t ht
    simpa only [one_div] using div_le_div_of_nonneg_right (Real.one_sub_inv_le_log_of_pos (hp t ht).2) (hp t ht).1.le
  rw [he, intervalIntegral.integral_symm] at hl
  change -lSmallUpper A ≤ -fourthRowClassicalL A at hl
  linarith only [hl]

#print axioms j_lower
#print axioms l_upper
#print axioms l_small_upper
end
end Wu04FullPsiClassical
