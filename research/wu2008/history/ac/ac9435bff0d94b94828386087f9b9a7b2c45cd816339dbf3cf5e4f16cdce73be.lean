import E08DebitLog

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval
open OriginalU8.SymbolicSmallGain (a b a_lt_b)

namespace WuTarget.E08Debit

def smallWeightLower : ℝ :=
  b * splitLower U8ActualThreshold.ratio - (b-a)/(1-a)

def smallSlope : ℝ := 3/(2-3*a)

def smallMomentLower : ℝ := (b-a)^3/(3*b*(1-a)^2)

def smallGain : ℝ :=
  2 * splitLower (2-3*b) * smallWeightLower + 2 * smallSlope * smallMomentLower

theorem small_weight_lower : smallWeightLower ≤ U8ActualThreshold.weightMass := by
  have h := (split_bounds (show (1 : ℝ) ≤ U8ActualThreshold.ratio by
    norm_num [U8ActualThreshold.ratio, a, b])).1
  unfold smallWeightLower U8ActualThreshold.weightMass
  have hb : 0 ≤ b := by norm_num [b]
  linarith only [mul_le_mul_of_nonneg_left h hb]

theorem small_log_affine {t : ℝ} (ht : t ∈ Icc a b) :
    splitLower (2-3*b) + smallSlope * (b-t) ≤ log (2-3*t) := by
  have hp : 0 < 2-3*b := by norm_num [b]
  have hq : 0 < 2-3*t := by linarith [ht.2]
  have h := log_le_sub_one_of_pos (div_pos hp hq)
  rw [log_div hp.ne' hq.ne'] at h
  have he : (2-3*b)/(2-3*t)-1 = -(3*(b-t)/(2-3*t)) := by
    field_simp
    ring
  rw [he] at h
  have hd := div_le_div_of_nonneg_left
    (show 0 ≤ 3*(b-t) by linarith [ht.2]) hq
    (show 2-3*t ≤ 2-3*a by linarith [ht.1])
  have hl := (split_bounds (by norm_num [b] : (1 : ℝ) ≤ 2-3*b)).1
  unfold smallSlope
  rw [show 3/(2-3*a)*(b-t) = 3*(b-t)/(2-3*a) by ring]
  linarith only [h, hd, hl]

theorem small_denominator {t : ℝ} (ht : t ∈ Icc a b) :
    t*(1-t)^2 ≤ b*(1-a)^2 := by
  obtain ⟨hp,hq,_⟩ := U8ActualThreshold.domain ht
  have hs : (1-t)^2 ≤ (1-a)^2 :=
    pow_le_pow_left₀ hq.le (by linarith [ht.1]) 2
  exact (mul_le_mul_of_nonneg_left hs hp.le).trans
    (mul_le_mul_of_nonneg_right ht.2 (sq_nonneg _))

theorem small_moment_pointwise {t : ℝ} (ht : t ∈ Icc a b) :
    (b-t)^2/(b*(1-a)^2) ≤ U8ActualThreshold.weight t * (b-t) := by
  obtain ⟨hp,hq,_⟩ := U8ActualThreshold.domain ht
  have h := div_le_div_of_nonneg_left (sq_nonneg (b-t))
    (mul_pos hp (sq_pos_of_pos hq)) (small_denominator ht)
  calc
    _ ≤ (b-t)^2/(t*(1-t)^2) := h
    _ = U8ActualThreshold.weight t * (b-t) := by
      unfold U8ActualThreshold.weight
      ring

theorem small_quadratic_integral :
    (∫ t in a..b, (b-t)^2/(b*(1-a)^2)) = smallMomentLower := by
  have hi : IntervalIntegrable (fun t : ℝ => (b-t)^2/(b*(1-a)^2)) volume a b :=
    (by fun_prop : Continuous (fun t : ℝ => (b-t)^2/(b*(1-a)^2))).intervalIntegrable a b
  have hd (t : ℝ) :
      HasDerivAt (fun t : ℝ => -(b-t)^3/(3*b*(1-a)^2))
        ((b-t)^2/(b*(1-a)^2)) t := by
    convert ((((hasDerivAt_const t b).sub (hasDerivAt_id t)).pow 3).neg.div_const
      (3*b*(1-a)^2)) using 1 <;> first | rfl | (dsimp; field_simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
  unfold smallMomentLower
  simp <;> ring

theorem small_gain_lower :
    smallGain ≤ 2 * (U8CanonicalMother.L-U8CanonicalMother.I) := by
  have hs : 0 ≤ smallSlope := by norm_num [smallSlope, a]
  have hl : 0 ≤ splitLower (2-3*b) := by
    norm_num [splitLower, SharpLogRecurrence.lowerLog, b]
  have hp (t : ℝ) (ht : t ∈ Icc a b) :
      splitLower (2-3*b) * U8ActualThreshold.weight t +
        smallSlope * ((b-t)^2/(b*(1-a)^2)) ≤
          (b-t)*log (2-3*t)/(t*(1-t)^2) := by
    have hw := mul_le_mul_of_nonneg_left (small_log_affine ht)
      (U8ActualThreshold.weight_nonneg ht)
    have hm := mul_le_mul_of_nonneg_left (small_moment_pointwise ht) hs
    calc
      _ ≤ splitLower (2-3*b) * U8ActualThreshold.weight t +
          smallSlope * (U8ActualThreshold.weight t * (b-t)) :=
        add_le_add le_rfl hm
      _ = U8ActualThreshold.weight t *
          (splitLower (2-3*b) + smallSlope * (b-t)) := by ring
      _ ≤ U8ActualThreshold.weight t * log (2-3*t) := hw
      _ = _ := by unfold U8ActualThreshold.weight; ring
  have hiq : IntervalIntegrable (fun t : ℝ => (b-t)^2/(b*(1-a)^2)) volume a b :=
    (by fun_prop : Continuous (fun t : ℝ => (b-t)^2/(b*(1-a)^2))).intervalIntegrable a b
  have hi := intervalIntegral.integral_mono_on a_lt_b.le
    ((U8ActualThreshold.weight_integrable.const_mul (splitLower (2-3*b))).add
      (hiq.const_mul smallSlope)) OriginalU8.SymbolicSmallGain.gain_integrable hp
  rw [intervalIntegral.integral_add
      (U8ActualThreshold.weight_integrable.const_mul _) (hiq.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    U8ActualThreshold.weight_integral, small_quadratic_integral] at hi
  have hwl := mul_le_mul_of_nonneg_left small_weight_lower hl
  change smallGain ≤
    2*(OriginalU8.SymbolicSmallGain.L-OriginalU8.Weighted.originalSmallIntegral)
  rw [OriginalU8.SymbolicSmallGain.gain_identity]
  unfold smallGain
  linarith only [hi, hwl]

theorem smallGain_exact : smallGain =
    (1511522572912035722939436549667987 /
      314528535306929036522961705755435700 : ℝ) := by
  norm_num [smallGain, smallWeightLower, smallSlope, smallMomentLower,
    U8ActualThreshold.ratio, a, b, splitLower, SharpLogRecurrence.lowerLog]

theorem smallGain_improves :
    U8ActualThreshold.gainLower + (1/5000 : ℝ) < smallGain := by
  rw [smallGain_exact, U8ActualThreshold.gainLower_exact]
  norm_num

end WuTarget.E08Debit
