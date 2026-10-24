import WR2ClassicalFifthSource
import WSrcFourEnclosureLogs

noncomputable section
namespace WuPaper.ClassicalFifthRational
open Real
open WuSource.SrcFourEnclosure (logLo log_bounds)
open ClassicalFifthSource ClassicalFifthKernel ClassicalCPolynomial

def value (extra ratio s : ℝ) : ℝ :=
  (logLo (s-1)+extra)*logLo ratio/(s*(1/2-(100/1327)*s))
def initialValue (s : ℝ) : ℝ := value 0 (ClassicalSixthBranch.r/ClassicalSixthBranch.v s) s
def middleValue (s : ℝ) : ℝ := value (cPoly (s-4)) (ClassicalSixthBranch.r/ClassicalSixthBranch.v s) s
def terminalValue (s : ℝ) : ℝ := value (cPoly (s-4)) (ClassicalSixthBranch.u s) s

theorem value_le {A : ℝ → ℝ} {extra ratio s : ℝ} (hr : 1 ≤ ratio)
    (hs : lo ≤ s) (he : s ≤ hi) (hA : logLo (s-1)+extra ≤ A s) (hA0 : 0 ≤ A s) :
    value extra ratio s ≤ A s*log ratio*ClassicalFourth.weight s := by
  have hL := log_bounds hr
  have hs0 : 0 < s := by linarith [geometry.1]
  have hden : 0 < (1:ℝ)/2-(100/1327)*s := by
    norm_num [hi,ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R] at he ⊢
    linarith
  have hw : ClassicalFourth.R-s ≠ 0 := by linarith [he.trans geometry.2.2.2.2.2]
  rw [ClassicalFourth.weight_literal hs0.ne' hw,mul_one_div]
  exact div_le_div_of_nonneg_right (mul_le_mul hA hL.2.1 hL.1 hA0) (mul_pos hs0 hden).le

private theorem lower_ratio_ge {s : ℝ} (hs : lo ≤ s) (he : s ≤ cut) :
    1 ≤ ClassicalSixthBranch.r/ClassicalSixthBranch.v s := by
  have h := ClassicalFifthBranch.lower_geometry hs he
  exact (le_div_iff₀ (by linarith [h.1])).mpr (by linarith [h.2])

private theorem initial_nonneg {s : ℝ} (hs : lo ≤ s) : 0 ≤ ClassicalFifthProfile.initial s :=
  log_nonneg (by linarith [geometry.1])

private theorem terminal_nonneg {s : ℝ} (hs : 4 ≤ s) (he : s ≤ hi) :
    0 ≤ ClassicalFifthProfile.terminal s := by
  exact add_nonneg (initial_nonneg (geometry.2.1.trans hs))
    (cPoly_nonneg (by linarith) (by linarith [he.trans geometry.2.2.2.2.1]))

theorem initial_value_le {s : ℝ} (hs : lo ≤ s) (he : s ≤ 4) :
    initialValue s ≤ kernel ClassicalFifthProfile.initial ClassicalFifthBranch.lower s := by
  have hp := (log_bounds (show 1 ≤ s-1 by linarith [geometry.1])).2.1
  have hh := value_le (A := ClassicalFifthProfile.initial) (extra := 0) (lower_ratio_ge hs (he.trans geometry.2.2.1))
    hs (he.trans (geometry.2.2.1.trans geometry.2.2.2.1)) (by simpa only [add_zero,ClassicalFifthProfile.initial,ClassicalSixthKernel.logFactor] using hp) (initial_nonneg hs)
  unfold initialValue kernel ClassicalFifthKernel.inner ClassicalFifthBranch.lower
  convert hh using 1
  ring

theorem middle_value_le {s : ℝ} (hs : 4 ≤ s) (he : s ≤ cut) :
    middleValue s ≤ kernel ClassicalFifthProfile.terminal ClassicalFifthBranch.lower s := by
  have hslo := geometry.2.1.trans hs
  have hp := (log_bounds (show 1 ≤ s-1 by linarith)).2.1
  have hA : logLo (s-1)+cPoly (s-4) ≤ ClassicalFifthProfile.terminal s := by
    change logLo (s-1)+cPoly (s-4) ≤ log (s-1)+cPoly (s-4)
    linarith only [hp]
  have hh := value_le (lower_ratio_ge hslo he) hslo (he.trans geometry.2.2.2.1) hA
    (terminal_nonneg hs (he.trans geometry.2.2.2.1))
  unfold middleValue kernel ClassicalFifthKernel.inner ClassicalFifthBranch.lower
  convert hh using 1
  ring

theorem terminal_value_le {s : ℝ} (hs : cut ≤ s) (he : s ≤ hi) :
    terminalValue s ≤ kernel ClassicalFifthProfile.terminal ClassicalFifthBranch.upper s := by
  have hs4 := geometry.2.2.1.trans hs
  have hslo := geometry.2.1.trans hs4
  have hp := (log_bounds (show 1 ≤ s-1 by linarith)).2.1
  have hA : logLo (s-1)+cPoly (s-4) ≤ ClassicalFifthProfile.terminal s := by
    change logLo (s-1)+cPoly (s-4) ≤ log (s-1)+cPoly (s-4)
    linarith only [hp]
  have hh := value_le (ClassicalFifthBranch.upper_geometry hs he).1 hslo he hA (terminal_nonneg hs4 he)
  unfold terminalValue kernel ClassicalFifthKernel.inner ClassicalFifthBranch.upper
  convert hh using 1
  ring

end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_value_le
#print axioms WuPaper.ClassicalFifthRational.middle_value_le
#print axioms WuPaper.ClassicalFifthRational.terminal_value_le
