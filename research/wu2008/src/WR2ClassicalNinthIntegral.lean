import WR2ClassicalNinthBounds
import WR2ClassicalLogSplit
import Wu08TerminalAlignment

noncomputable section
namespace WuPaper.ClassicalNinth
open Real Set MeasureTheory Wu2008DoubleSieve Wu08TerminalAlignment ClassicalLogRatio
open scoped Interval

abbrev lowerEndpoint : ℝ := ninthProfileK2
abbrev upperEndpoint : ℝ := ninthProfileSigma

theorem sigma_bounds : upperEndpoint ∈ Icc (3/11) (3/10) := by
  norm_num [upperEndpoint,ninthProfileSigma,ninthProfileK1]

theorem domain {t : ℝ} (ht : t ∈ Icc lowerEndpoint upperEndpoint) : t ∈ Icc (3/25) (3/10) := by
  have hl : (3/25:ℝ) ≤ lowerEndpoint := by norm_num [lowerEndpoint,ninthProfileK2]
  exact ⟨hl.trans ht.1,ht.2.trans sigma_bounds.2⟩

theorem ninth_integral : ninthMain =
    8*∫ t in lowerEndpoint..upperEndpoint, kernel (1-upperEndpoint) (-1) upperEndpoint 0 t := by
  unfold ninthMain J9
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have he : lowerEndpoint ≤ upperEndpoint := by
    norm_num [lowerEndpoint,upperEndpoint,ninthProfileK2,ninthProfileSigma,ninthProfileK1]
  rw [uIcc_of_le he] at ht
  have hd := domain ht
  have hs := sigma_bounds
  dsimp only
  have h := kernel_literal (1-upperEndpoint) (-1) upperEndpoint 0
    (by linarith [hd.1] : t ≠ 0) (by linarith [hd.2] : 1-t ≠ 0)
    (by linarith [hd.2,hs.2] : 1-upperEndpoint+(-1)*t ≠ 0)
    (by linarith [hs.1] : upperEndpoint+0*t ≠ 0)
  simpa only [neg_one_mul,zero_mul,add_zero,← sub_eq_add_neg] using h.symm

def upperValue (t : ℝ) : ℝ :=
  WuSource.SrcFourEnclosure.logHi ((1-upperEndpoint-t)/upperEndpoint)/(t*(1-t))

theorem kernel_le_upper {t : ℝ} (ht : t ∈ Icc (3/25) (3/10)) :
    kernel (1-upperEndpoint) (-1) upperEndpoint 0 t ≤ upperValue t := by
  have hs := sigma_bounds
  have ht0 : 0 < t := by linarith [ht.1]
  have ht1 : 0 < 1-t := by linarith [ht.2]
  have hs0 : 0 < upperEndpoint := by linarith [hs.1]
  have hr : 1 ≤ (1-upperEndpoint-t)/upperEndpoint :=
    (one_le_div hs0).mpr (by linarith [hs.2,ht.2])
  have h := kernel_literal (1-upperEndpoint) (-1) upperEndpoint 0 ht0.ne' ht1.ne'
    (by linarith [hs.2,ht.2] : 1-upperEndpoint+(-1)*t ≠ 0)
    (by linarith : upperEndpoint+0*t ≠ 0)
  simp only [neg_one_mul,zero_mul,add_zero,← sub_eq_add_neg] at h
  rw [h]
  exact div_le_div_of_nonneg_right (WuSource.SrcFourEnclosure.log_bounds hr).2.2 (mul_pos ht0 ht1).le

end WuPaper.ClassicalNinth
#print axioms WuPaper.ClassicalNinth.ninth_integral
#print axioms WuPaper.ClassicalNinth.kernel_le_upper
