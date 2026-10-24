import Wu08TerminalAlignment
import MathlibNt.Wu2008DoubleSieve.ClassicalSingleBounds
import WR2ClassicalLogSplit

noncomputable section
namespace WuPaper.ClassicalThirdFourth
open Real Set MeasureTheory Wu2008DoubleSieve Wu08TerminalAlignment
open ClassicalSingleBounds
open scoped Interval

/-- The third slot extends the fourth by an interval where the sieve function is exactly one. -/
theorem third_eq_fourth_add : thirdMain = fourthMain+8*log (1200/727) := by
  have hp := truncatedSixthLower_parameters
  have has : a ≤ s := hp.2.1.le.trans hp.2.2.1.le
  have hs3 : s ≤ (1:ℝ)/3 := hp.2.2.2.1.le
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (g_integrable le_rfl hs3 has) (g_integrable has le_rfl hs3)
  have h1 : thirdMain = 4*∫ t in a..(1/3:ℝ), g t := by
    simp only [thirdMain,SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,g,a]
  have h2 : fourthMain = 4*∫ t in a..s, g t := by
    simp only [fourthMain,SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,g,a,s]
  rw [h1,h2,← hadd,high_integral_eq]
  have he : 6*a/s = (1200:ℝ)/727 := by
    norm_num [a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  rw [he]
  ring

theorem difference_upper : 8*log ((1200:ℝ)/727) ≤ (4009203:ℝ)/1000000 := by
  have h := (WuSource.SrcFourEnclosure.log_bounds (by norm_num : (1:ℝ) ≤ 1200/727)).2.2
  have hp : 8*WuSource.SrcFourEnclosure.logHi ((1200:ℝ)/727) ≤ (4009203:ℝ)/1000000 := by
    norm_num [WuSource.SrcFourEnclosure.logHi,WuSource.SrcFourEnclosure.logLo,Finset.sum_range_succ]
  linarith only [h,hp]

/-- Only the fourth slot needs numerical integration; the remaining interval is explicit. -/
theorem third_upper_of_fourth (h : fourthMain ≤ (1964373:ℝ)/100000) :
    thirdMain ≤ (23652933:ℝ)/1000000 := by
  rw [third_eq_fourth_add]
  linarith only [h,difference_upper]

end WuPaper.ClassicalThirdFourth
#print axioms WuPaper.ClassicalThirdFourth.third_eq_fourth_add
#print axioms WuPaper.ClassicalThirdFourth.third_upper_of_fourth
