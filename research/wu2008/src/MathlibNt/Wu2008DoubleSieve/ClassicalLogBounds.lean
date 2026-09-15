import MathlibNt.Wu2008DoubleSieve.ClassicalAnalyticLeaves
import MathlibNt.Wu2008DoubleSieve.FourSeventhsLog

namespace Wu2008DoubleSieve.ClassicalLogBounds
open Real Set MeasureTheory ClassicalAnalyticLeaves
open scoped Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- Integrating a reciprocal tangent gives a lower logarithm bound on every positive interval. -/
theorem log_tangent_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    2*(b-a)/(a+b) ≤ log b-log a := by
  have hab0 : 0 < a+b := by linarith
  have hi : (∫ x in a..b, 4/(a+b)-4*x/(a+b)^2) ≤ ∫ x in a..b, 1/x := by
    apply intervalIntegral.integral_mono_on hab
    · exact (by fun_prop : Continuous (fun x : ℝ => 4/(a+b)-4*x/(a+b)^2)).intervalIntegrable a b
    · exact (continuousOn_const.div continuousOn_id (fun x hx => by
        rw [uIcc_of_le hab] at hx
        exact (ha.trans_le hx.1).ne')).intervalIntegrable
    · intro x hx
      have hx0 := ha.trans_le hx.1
      apply (le_div_iff₀ hx0).2
      have hs : 0 ≤ (2*x-(a+b))^2 := sq_nonneg _
      field_simp
      nlinarith
  have he : (∫ x in a..b, 4/(a+b)-4*x/(a+b)^2) = 2*(b-a)/(a+b) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous (fun x : ℝ => 4*x/(a+b)^2)).intervalIntegrable a b),
      intervalIntegral.integral_const, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [he, integral_reciprocal ha hab] at hi
  exact hi

theorem log_three_lower : (38/35 : ℝ) ≤ log 3 := by
  have h1 := log_tangent_lower (a := (1 : ℝ)) (b := 3/2) (by norm_num) (by norm_num)
  have h2 := log_tangent_lower (a := (3/2 : ℝ)) (b := 2) (by norm_num) (by norm_num)
  have h3 := log_tangent_lower (a := (2 : ℝ)) (b := 3) (by norm_num) (by norm_num)
  norm_num at h1 h2 h3
  linarith

theorem log_two_upper : log 2 ≤ (17/24 : ℝ) := by
  have h1 := SecondFunctionalFourSevenths.log_chord_bound
    (a := (1 : ℝ)) (b := 3/2) (by norm_num) (by norm_num)
  have h2 := SecondFunctionalFourSevenths.log_chord_bound
    (a := (3/2 : ℝ)) (b := 2) (by norm_num) (by norm_num)
  rw [log_div (by norm_num) (by norm_num)] at h2
  norm_num at h1 h2
  linarith

/-- The lower delay function increases; only its value at four uses the initial formula. -/
theorem lower_linear_four {s : ℝ} (hs : 4 ≤ s) :
    s/4*log 3 ≤ wuLowerCoefficient s := by
  have hf := monotoneOn_jr1965f (by norm_num : (4 : ℝ) ∈ Ioi 0)
    (show s ∈ Ioi 0 by change 0 < s; linarith) hs
  rw [jr1965f_eq_log_firstInterval (by norm_num) le_rfl] at hf
  norm_num only [show (4 : ℝ)-1=3 by norm_num] at hf
  have he : 0 < 2 * exp eulerMascheroniConstant := by positivity
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hf (by linarith : 0 ≤ s)) he.le
  change _ ≤ wuLowerCoefficient s at hm
  convert hm using 1
  field_simp

theorem base_linear_lower :
    (961/20 : ℝ)*log 3 ≤
      24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
      8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) := by
  have h1 := lower_linear_four (s := 1/(2*truncatedSixthLowerAlpha)) (by
    norm_num [truncatedSixthLowerAlpha])
  have h2 := lower_linear_four (s := 1/(2*truncatedSixthLowerBeta)) (by
    norm_num [truncatedSixthLowerBeta])
  norm_num [truncatedSixthLowerAlpha, truncatedSixthLowerBeta] at h1 h2 ⊢
  linarith

theorem base_gt_fifty_two :
    (52 : ℝ) < 24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
      8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) := by
  have h := base_linear_lower
  have hl := log_three_lower
  linarith

/-- The actual upper delay function is antitone, unlike Buchstab. -/
theorem upper_div_le_third {s : ℝ} (hs : 3 ≤ s) : wuUpperCoefficient s / s ≤ 1/3 := by
  have hs0 : 0 < s := by linarith
  rw [wuUpperCoefficient_div hs0.ne']
  have hf := antitoneOn_jr1965F (by norm_num : (3 : ℝ) ∈ Ioi 0) hs0 hs
  rw [jr1965F_eq_of_le_three (le_rfl : (3 : ℝ) ≤ 3)] at hf
  have hd : 0 < 2*exp eulerMascheroniConstant := by positivity
  exact (div_le_iff₀ hd).2 (by linarith)

end Wu2008DoubleSieve.ClassicalLogBounds
