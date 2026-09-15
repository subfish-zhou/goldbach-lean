import MathlibNt.Wu2008DoubleSieve.ClassicalSingleBounds
import MathlibNt.Wu2008DoubleSieve.ClassicalFourBounds

namespace Wu2008DoubleSieve.ClassicalRemainingBounds
open Real Set MeasureTheory ClassicalAnalyticLeaves ClassicalLogBounds
open scoped Interval

/-- Exact primitive for the rational majorants on the original positive windows. -/
theorem rational_integral {a b A B C : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ t in a..b, A/t + B/(1-t) + C/t^2) =
      A*(log b-log a) - B*(log (1-b)-log (1-a)) - C*(1/b-1/a) := by
  have hi : IntervalIntegrable (fun t => A/t+B/(1-t)+C/t^2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact continuousOn_const.div continuousOn_id (fun t ht => by
          rw [uIcc_of_le hab] at ht; exact (ha.trans_le ht.1).ne')
      · exact continuousOn_const.div (continuousOn_const.sub continuousOn_id) (fun t ht => by
          rw [uIcc_of_le hab] at ht; linarith [ht.2])
    · exact continuousOn_const.div (continuousOn_id.pow 2) (fun t ht => by
        rw [uIcc_of_le hab] at ht; exact pow_ne_zero _ (ha.trans_le ht.1).ne')
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun t => A*log t-B*log (1-t)-C/t) (A/t+B/(1-t)+C/t^2) t := by
    rw [uIcc_of_le hab] at ht
    have ht0 := ha.trans_le ht.1
    have ht1 : 1-t ≠ 0 := by linarith [ht.2]
    have h := (((hasDerivAt_log ht0.ne').const_mul A).sub
      ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).log ht1).const_mul B)).sub
      ((hasDerivAt_const t C).div (hasDerivAt_id t) ht0.ne')
    convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [he]
  ring

theorem J7_log_upper : SeventhEighth.J7 ≤
    1/SeventhEighth.sigma-3 -
      2*log ((1-SeventhEighth.sigma)/(2*SeventhEighth.sigma)) := by
  let s := SeventhEighth.sigma
  have hs0 : 0 < s := by norm_num [s, SeventhEighth.sigma, SeventhEighth.alpha]
  have hs : s ≤ (1/3 : ℝ) := SeventhEighth.classical_parameters.2.2.le
  have hi : IntervalIntegrable (fun t : ℝ => (-2)/t+(-2)/(1-t)+1/t^2) volume s (1/3) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact continuousOn_const.div continuousOn_id (fun t ht => by
          rw [uIcc_of_le hs] at ht; exact (hs0.trans_le ht.1).ne')
      · exact continuousOn_const.div (continuousOn_const.sub continuousOn_id) (fun t ht => by
          rw [uIcc_of_le hs] at ht; linarith [ht.2])
    · exact continuousOn_const.div (continuousOn_id.pow 2) (fun t ht => by
        rw [uIcc_of_le hs] at ht; exact pow_ne_zero _ (hs0.trans_le ht.1).ne')
  have h := intervalIntegral.integral_mono_on hs SeventhEighth.J7_integrable hi (fun t ht => by
    have ht0 := hs0.trans_le ht.1
    have hd : 0 < 1-t := by linarith [ht.2]
    have hr : 0 < (1-2*t)/t := div_pos (by linarith [ht.2]) ht0
    have hh := div_le_div_of_nonneg_right (log_le_sub_one_of_pos hr) (mul_pos ht0 hd).le
    convert hh using 1 <;> first | rfl | (field_simp; ring))
  rw [rational_integral hs0 hs (by norm_num)] at h
  have hl := log_div (show 1-s ≠ 0 by linarith) (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hs0.ne')
  have hm := log_mul (by norm_num : (2 : ℝ) ≠ 0) hs0.ne'
  have he : log (1-(1/3 : ℝ))-log (1/3 : ℝ) = log 2 := by
    rw [← log_div (by norm_num) (by norm_num)]
    norm_num
  change SeventhEighth.J7 ≤ _
  change _ ≤ 1/s-3-2*log ((1-s)/(2*s))
  norm_num only [one_div_div] at h
  change SeventhEighth.J7 ≤ _ at h
  norm_num only [show (1-(1/3 : ℝ)) = 2/3 by norm_num] at he
  linarith

theorem J8_log_upper : SeventhEighth.J8 ≤
    log ((1/3)/SeventhEighth.alpha) -
      2*log ((1-SeventhEighth.alpha)/(2/3)) := by
  let a := SeventhEighth.alpha
  have ha : 0 < a := SeventhEighth.classical_parameters.1
  have hab : a ≤ (1/3 : ℝ) :=
    SeventhEighth.classical_parameters.2.1.le.trans SeventhEighth.classical_parameters.2.2.le
  have hi : IntervalIntegrable (fun t : ℝ => 1/t+(-2)/(1-t)+0/t^2) volume a (1/3) := by
    simp only [zero_div, add_zero]
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.div continuousOn_id (fun t ht => by
      rw [uIcc_of_le hab] at ht; exact (ha.trans_le ht.1).ne')).add
      (continuousOn_const.div (continuousOn_const.sub continuousOn_id) (fun t ht => by
        rw [uIcc_of_le hab] at ht; linarith [ht.2]))
  have h := intervalIntegral.integral_mono_on hab SeventhEighth.J8_integrable hi (fun t ht => by
    have ht0 := ha.trans_le ht.1
    have hd : 0 < 1-t := by linarith [ht.2]
    have hh := div_le_div_of_nonneg_right
      (log_le_sub_one_of_pos (show 0 < 2-3*t by linarith [ht.2])) (mul_pos ht0 hd).le
    convert hh using 1 <;> first | rfl | (field_simp; ring))
  rw [rational_integral ha hab (by norm_num)] at h
  change SeventhEighth.J8 ≤ log ((1/3)/a)-2*log ((1-a)/(2/3))
  rw [log_div (by norm_num : (1/3 : ℝ) ≠ 0) ha.ne',
    log_div (show 1-a ≠ 0 by norm_num [a, SeventhEighth.alpha])
      (by norm_num : (2/3 : ℝ) ≠ 0)]
  norm_num only [show (1-(1/3 : ℝ)) = 2/3 by norm_num] at h
  convert h using 1 <;> first | rfl | ring

theorem J9_log_upper : J9 ≤
    ((1-2*ninthProfileSigma)/ninthProfileSigma)*log (ninthProfileSigma/ninthProfileK2) -
      2*log ((1-ninthProfileK2)/(1-ninthProfileSigma)) := by
  let a := ninthProfileK2
  let b := ninthProfileSigma
  let A := (1-2*b)/b
  have ha : 0 < a := by have hp := ninthMain_parameters; dsimp [a]; linarith
  have hb0 : 0 < b := by have hp := ninthMain_parameters; dsimp [b]; linarith
  have hab : a ≤ b := ninthMain_parameters.2.1.le
  have hb : b < 1 := by have hp := ninthMain_parameters; dsimp [b]; linarith
  have hi : IntervalIntegrable (fun t : ℝ => A/t+(-2)/(1-t)+0/t^2) volume a b := by
    simp only [zero_div, add_zero]
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.div continuousOn_id (fun t ht => by
      rw [uIcc_of_le hab] at ht; exact (ha.trans_le ht.1).ne')).add
      (continuousOn_const.div (continuousOn_const.sub continuousOn_id) (fun t ht => by
        rw [uIcc_of_le hab] at ht; linarith [ht.2]))
  have h := intervalIntegral.integral_mono_on hab J9_integrable hi (fun t ht => by
    have ht0 := ha.trans_le ht.1
    have hd : 0 < 1-t := by linarith [ht.2]
    have hr : 0 < (1-b-t)/b := by
      apply div_pos _ hb0
      have hb3 : b < 3/10 := ninthMain_parameters.2.2.2
      linarith [ht.2]
    have hh := div_le_div_of_nonneg_right (log_le_sub_one_of_pos hr) (mul_pos ht0 hd).le
    convert hh using 1 <;> first | rfl | (dsimp [A]; field_simp; ring))
  rw [rational_integral ha hab hb] at h
  change J9 ≤ A*log (b/a)-2*log ((1-a)/(1-b))
  rw [log_div hb0.ne' ha.ne', log_div (by linarith) (by linarith)]
  convert h using 1 <;> first | rfl | ring

/-- A fixed factor-of-two decomposition, using only the accepted universal chord bound. -/
theorem log_scaled_two_upper {x : ℝ} (hx : 2 ≤ x) :
    log x ≤ 17/24 + ((x/2)-1)*((x/2)+1)/(2*(x/2)) := by
  have hx0 : 0 < x/2 := by linarith
  have h := SecondFunctionalFourSevenths.log_chord_bound
    (a := (1 : ℝ)) (b := x/2) (by norm_num) (by linarith)
  have he : log x = log 2 + log (x/2) := by
    rw [← log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
    congr 1
    ring
  norm_num only [log_one, div_one, mul_one, one_mul] at h
  rw [he]
  have heq : (x/2-1)*(1+1/(x/2))/2 = (x/2-1)*(x/2+1)/(2*(x/2)) := by
    field_simp
  rw [heq] at h
  have hh := log_two_upper
  linarith

theorem J7_lt_tenth : SeventhEighth.J7 < (1/10 : ℝ) := by
  have h := J7_log_upper
  have hl := log_tangent_lower (a := (1 : ℝ))
    (b := (1-SeventhEighth.sigma)/(2*SeventhEighth.sigma)) (by norm_num)
    (by norm_num [SeventhEighth.sigma, SeventhEighth.alpha])
  norm_num [SeventhEighth.sigma, SeventhEighth.alpha] at h hl
  linarith

theorem J8_lt_seven_eighths : SeventhEighth.J8 < (7/8 : ℝ) := by
  have h := J8_log_upper
  have hc := SecondFunctionalFourSevenths.log_chord_bound
    (a := (1 : ℝ)) (b := (1/3)/(4*SeventhEighth.alpha)) (by norm_num)
    (by norm_num [SeventhEighth.alpha])
  have hl := log_tangent_lower (a := (1 : ℝ))
    (b := (1-SeventhEighth.alpha)/(2/3)) (by norm_num)
    (by norm_num [SeventhEighth.alpha])
  have he : log ((1/3)/SeventhEighth.alpha) =
      2*log 2+log ((1/3)/(4*SeventhEighth.alpha)) := by
    have hm := log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num [SeventhEighth.alpha] : (1/3)/(4*SeventhEighth.alpha) ≠ 0)
    have hp := log_pow (2 : ℝ) 2
    norm_num at hp
    rw [show (4 : ℝ)*((1/3)/(4*SeventhEighth.alpha)) = (1/3)/SeventhEighth.alpha by ring] at hm
    linarith
  rw [he] at h
  have h2 := log_two_upper
  norm_num [SeventhEighth.alpha] at h hc hl
  linarith

theorem J9_lt_one : J9 < (1 : ℝ) := by
  have h := J9_log_upper
  have hc := log_scaled_two_upper (x := ninthProfileSigma/ninthProfileK2)
    (by norm_num [ninthProfileSigma, ninthProfileK1, ninthProfileK2])
  have hl := log_tangent_lower (a := (1 : ℝ))
    (b := (1-ninthProfileK2)/(1-ninthProfileSigma)) (by norm_num)
    (by norm_num [ninthProfileSigma, ninthProfileK1, ninthProfileK2])
  norm_num [ninthProfileSigma, ninthProfileK1, ninthProfileK2] at h hc hl
  linarith

/-- All original negative weights are consumed; this is not a positivity claim. -/
theorem complete_coefficient_gt_negative_twenty_three :
    (-23 : ℝ) < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := base_gt_fifty_two
  have hg := ClassicalSingleBounds.G_pair_lt_fifty_two
  have h4 := ClassicalFourBounds.four_weighted_lt_six
  have h7 := J7_lt_tenth
  have h8 := J8_lt_seven_eighths
  have h9 := J9_lt_one
  have hp := fifth_nonneg
  have hq := sixth_nonneg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient
  change _ < _
  change SingleUpperClassicalLimit.Glin (1/3) +
    SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma < 52 at hg
  linarith

end Wu2008DoubleSieve.ClassicalRemainingBounds
