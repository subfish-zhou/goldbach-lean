import WR2ClassicalEighthBounds
import WR2ClassicalLogSplit
import Wu08TerminalAlignment

noncomputable section
namespace WuPaper.ClassicalEighth
open Real Set MeasureTheory Wu2008DoubleSieve Wu08TerminalAlignment ClassicalLogRatio
open scoped Interval

abbrev lowerEndpoint : ℝ := SeventhEighth.alpha

theorem domain {t : ℝ} (ht : t ∈ Icc lowerEndpoint (1/3)) : t ∈ Icc (3/40) (1/3) := by
  have hs : (3/40:ℝ) ≤ lowerEndpoint := by norm_num [lowerEndpoint,SeventhEighth.alpha]
  exact ⟨hs.trans ht.1,ht.2⟩

theorem raw_integral : 8*SeventhEighth.J8 = 8*∫ t in lowerEndpoint..(1/3), kernel 2 (-3) 1 0 t := by
  unfold SeventhEighth.J8
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have he : lowerEndpoint ≤ (1/3:ℝ) := by norm_num [lowerEndpoint,SeventhEighth.alpha]
  rw [uIcc_of_le he] at ht
  have hd := domain ht
  dsimp only
  have h := kernel_literal 2 (-3) 1 0 (by linarith [hd.1] : t ≠ 0)
    (by linarith [hd.2] : 1-t ≠ 0) (by linarith [hd.2] : 2+(-3)*t ≠ 0)
    (by linarith [hd.1] : 1+0*t ≠ 0)
  simpa only [neg_mul,zero_mul,add_zero,div_one,← sub_eq_add_neg] using h.symm

def upperValue (t : ℝ) : ℝ :=
  WuSource.SrcFourEnclosure.logHi (2-3*t)/(t*(1-t))

theorem kernel_le_upper {t : ℝ} (ht : t ∈ Icc (3/40) (1/3)) :
    kernel 2 (-3) 1 0 t ≤ upperValue t := by
  have ht0 : 0 < t := by linarith [ht.1]
  have ht1 : 0 < 1-t := by linarith [ht.2]
  have hr : 1 ≤ 2-3*t := by linarith [ht.2]
  have h := kernel_literal 2 (-3) 1 0 ht0.ne' ht1.ne'
    (by linarith [ht.2] : 2+(-3)*t ≠ 0) (by linarith : 1+0*t ≠ 0)
  simp only [neg_mul,zero_mul,add_zero,div_one,← sub_eq_add_neg] at h
  rw [h]
  exact div_le_div_of_nonneg_right (WuSource.SrcFourEnclosure.log_bounds hr).2.2
    (mul_pos ht0 ht1).le

end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.raw_integral
#print axioms WuPaper.ClassicalEighth.kernel_le_upper
