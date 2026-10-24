import WR2ClassicalSixthKernel
import WSrcFourEnclosureLogs

noncomputable section
namespace WuPaper.ClassicalSixthRational
open Real WuSource.SrcFourEnclosure WuSource.SrcSixthGain
open ClassicalSixthBranch ClassicalSixthKernel

def value (ratio s : ℝ) : ℝ := logLo ratio*logLo (s-1)/(s*(1-2*QuarterTrim.alpha*s))
def lowerValue (s : ℝ) : ℝ := value (r*u s/v s) s
def upperValue (s : ℝ) : ℝ := value (u s*v s/r) s

theorem value_le {ratio s : ℝ} (hr : 1 ≤ ratio) (hs : 2 ≤ s) (he : s ≤ endpoint) :
    value ratio s ≤ log ratio*logFactor s*ClassicalSixthWeight.weight s := by
  have ha := WuSource.SrcFourEnclosure.log_bounds hr
  have hb := WuSource.SrcFourEnclosure.log_bounds (show 1 ≤ s-1 by linarith)
  have hs0 : 0 < s := by linarith
  have hden : 0 < 1-2*QuarterTrim.alpha*s := by
    norm_num [endpoint,QuarterTrim.alpha,QuarterTrim.beta] at he ⊢
    linarith
  have hw : ClassicalSixthWeight.R-s ≠ 0 := by
    norm_num [ClassicalSixthWeight.R,endpoint,QuarterTrim.alpha,QuarterTrim.beta] at he ⊢
    linarith
  rw [ClassicalSixthWeight.weight_literal hs0.ne' hw]
  change value ratio s ≤ log ratio*log (s-1)*(1/(s*(1-2*QuarterTrim.alpha*s)))
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right
    (mul_le_mul ha.2.1 hb.2.1 hb.1 (log_nonneg hr)) (mul_pos hs0 hden).le

theorem lower_value_le {s : ℝ} (hs : 2 ≤ s) (he : s ≤ split) :
    lowerValue s ≤ kernel lower s := by
  have hep : s ≤ endpoint := he.trans (by norm_num [split,endpoint,QuarterTrim.alpha,QuarterTrim.beta])
  have h := geometry hep
  have hv : 0 < v s := by linarith
  have hr : 1 ≤ r := by norm_num [r]
  have huv : v s ≤ u s := by dsimp [u,v]; linarith
  have hq : 1 ≤ r*u s/v s := by
    apply (le_div_iff₀ hv).mpr
    nlinarith [mul_le_mul_of_nonneg_right hr (show 0 ≤ u s by linarith [h.1])]
  have hh := value_le hq hs hep
  unfold lowerValue kernel ClassicalSixthKernel.inner lower
  convert hh using 1
  ring

theorem upper_value_le {s : ℝ} (hs : split ≤ s) (he : s ≤ endpoint) :
    upperValue s ≤ kernel upper s := by
  have h := geometry he
  have hr : 0 < r := by norm_num [r]
  have hq : 1 ≤ u s*v s/r := by
    apply (le_div_iff₀ hr).mpr
    nlinarith [mul_le_mul h.1 h.2 (by norm_num : (0:ℝ) ≤ 1) (by linarith : 0 ≤ u s)]
  have hs2 : 2 ≤ s := (by norm_num [split,QuarterTrim.alpha,QuarterTrim.beta] : (2:ℝ) ≤ split).trans hs
  have hh := value_le hq hs2 he
  unfold upperValue kernel ClassicalSixthKernel.inner upper
  convert hh using 1
  ring

end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_value_le
#print axioms WuPaper.ClassicalSixthRational.upper_value_le
