import WR2ClassicalSeventhBounds
import WR2ClassicalLogSplit
import Wu08TerminalAlignment

noncomputable section
namespace WuPaper.ClassicalSeventh
open Real Set MeasureTheory Wu2008DoubleSieve Wu08TerminalAlignment ClassicalLogRatio
open scoped Interval

abbrev lowerEndpoint : ℝ := SeventhEighth.sigma

theorem domain {t : ℝ} (ht : t ∈ Icc lowerEndpoint (1/3)) : t ∈ Icc (1/4) (1/3) := by
  have hs : (1/4:ℝ) ≤ lowerEndpoint := by norm_num [lowerEndpoint,SeventhEighth.sigma,SeventhEighth.alpha]
  exact ⟨hs.trans ht.1,ht.2⟩

theorem seventh_integral : seventhMain = 8*∫ t in lowerEndpoint..(1/3), kernel 1 (-2) 0 1 t := by
  unfold seventhMain SeventhEighth.J7
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have he : lowerEndpoint ≤ (1/3:ℝ) := by norm_num [lowerEndpoint,SeventhEighth.sigma,SeventhEighth.alpha]
  rw [uIcc_of_le he] at ht
  have hd := domain ht
  dsimp only
  have h := kernel_literal 1 (-2) 0 1 (by linarith [hd.1] : t ≠ 0)
    (by linarith [hd.2] : 1-t ≠ 0) (by linarith [hd.2] : 1+(-2)*t ≠ 0)
    (by linarith [hd.1] : 0+1*t ≠ 0)
  simpa only [neg_mul,one_mul,zero_add,← sub_eq_add_neg] using h.symm

def upperValue (t : ℝ) : ℝ :=
  WuSource.SrcFourEnclosure.logHi ((1-2*t)/t)/(t*(1-t))

theorem kernel_le_upper {t : ℝ} (ht : t ∈ Icc (1/4) (1/3)) :
    kernel 1 (-2) 0 1 t ≤ upperValue t := by
  have ht0 : 0 < t := by linarith [ht.1]
  have ht1 : 0 < 1-t := by linarith [ht.2]
  have hr : 1 ≤ (1-2*t)/t := (one_le_div ht0).mpr (by linarith [ht.2])
  have h := kernel_literal 1 (-2) 0 1 ht0.ne' ht1.ne'
    (by linarith [ht.2] : 1+(-2)*t ≠ 0) (by linarith : 0+1*t ≠ 0)
  simp only [neg_mul,one_mul,zero_add,← sub_eq_add_neg] at h
  rw [h]
  exact div_le_div_of_nonneg_right (WuSource.SrcFourEnclosure.log_bounds hr).2.2
    (mul_pos ht0 ht1).le

end WuPaper.ClassicalSeventh
#print axioms WuPaper.ClassicalSeventh.seventh_integral
#print axioms WuPaper.ClassicalSeventh.kernel_le_upper
