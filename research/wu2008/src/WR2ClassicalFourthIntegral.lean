import WR2ClassicalFourthWeight
import Wu08TerminalAlignment
import MathlibNt.Wu2008DoubleSieve.ClassicalSingleBounds

noncomputable section
namespace WuPaper.ClassicalFourth
open Real Set MeasureTheory Wu2008DoubleSieve Wu08TerminalAlignment
open scoped Interval

/-- Affine substitution puts all B,C,D tables on their original recurrence parameter. -/
theorem fourth_integral : fourthMain =
    4*∫ s in (3:ℝ)..(R-1), weight s*wuUpperCoefficient s := by
  let a : ℝ := 100/1327
  have ha : a ≠ 0 := by norm_num [a]
  have hend : (1:ℝ)/2-a*(R-1) = a := by norm_num [a,R]
  have hstart : (1:ℝ)/2-a*3 = truncatedSixthLowerSigma := by
    norm_num [a,truncatedSixthLowerSigma,truncatedSixthLowerAlpha]
  have htrans := intervalIntegral.smul_integral_comp_sub_mul (f := ClassicalSingleBounds.g)
    (a := (3:ℝ)) (b := R-1) a ((1:ℝ)/2)
  rw [hend,hstart] at htrans
  have hf : fourthMain = 4*∫ t in a..truncatedSixthLowerSigma, ClassicalSingleBounds.g t := by
    simp only [fourthMain,SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,
      sub_zero,ClassicalSingleBounds.g,ClassicalSingleBounds.a,a,truncatedSixthLowerAlpha]
  rw [hf,← htrans]
  simp only [smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (by norm_num [R] : (3:ℝ) ≤ R-1)] at hs
  have hs0 : s ≠ 0 := by linarith [hs.1]
  have hr : R-s ≠ 0 := by linarith [hs.2]
  dsimp only
  rw [weight_literal hs0 hr]
  have hid : ((1:ℝ)/2-((1:ℝ)/2-a*s))/truncatedSixthLowerAlpha = s := by
    norm_num [a,truncatedSixthLowerAlpha]
  unfold ClassicalSingleBounds.g
  rw [hid]
  have hd : (1:ℝ)/2-a*s ≠ 0 := by
    intro h
    apply hr
    dsimp [R,a] at *
    linarith only [h]
  have he : (1:ℝ)/2-((1:ℝ)/2-a*s) = a*s := by ring
  rw [he]
  dsimp [a] at hd ⊢
  field_simp [hs0,hd]

end WuPaper.ClassicalFourth
#print axioms WuPaper.ClassicalFourth.fourth_integral
