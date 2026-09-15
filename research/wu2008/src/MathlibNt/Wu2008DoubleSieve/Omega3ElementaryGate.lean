import MathlibNt.Wu2008DoubleSieve.FourSeventhsElementaryFeedback
import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralEnvelope

namespace Wu2008DoubleSieve.Omega3ElementaryGate
open Set LiLiuPrereqBuchstab

/-- The fixed sufficient gate, with no parameter optimization. -/
theorem argument_ge {s φ a b c : ℝ} (hs : 19/8 ≤ s) (hφ : 2 ≤ φ)
    (ha : a ≤ 1/s) (hb : b ≤ 1/s) (hc : c ≤ 1/s) (hb0 : 0 < b) :
    7/4 ≤ (φ-a-b-c)/b := by
  have hs0 : 0 < s := by linarith
  have hcap : (19/4 : ℝ) * (1/s) ≤ 2 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hs0).mpr
    linarith
  apply (le_div_iff₀ hb0).mpr
  linarith

/-- The actual kernel, with its selected middle coordinate squared. -/
theorem kernel_le {s φ a b c : ℝ} (hs : 19/8 ≤ s) (hφ : 2 ≤ φ)
    (ha : a ≤ 1/s) (hb : b ≤ 1/s) (hc : c ≤ 1/s)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) :
    omega3XIntegralKernel φ a b c ≤ (4/7) * (1/(a*b^2*c)) := by
  have h := SecondFunctionalFourSevenths.buchstab_le_four_sevenths
    (argument_ge hs hφ ha hb hc hb0)
  unfold omega3XIntegralKernel
  calc
    _ ≤ (4/7)/(a*b^2*c) := div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by ring

end Wu2008DoubleSieve.Omega3ElementaryGate
