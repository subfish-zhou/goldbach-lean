import Hf4AmountPublic

noncomputable section
namespace Hf4Actual
open Real Set

theorem gap_factor {x : ℝ} (hx : 1 ≤ x) :
    RemainingHf.basicUpper x-RemainingHf.basicLower x =
    (1/105:ℝ)*((x-1)/x)^2*((x-1)/(x+1))^4*(x-1)^2*((9*x+5)/(x^2+8*x+1)) := by
  rw [← Hf4Quad.up_eq hx, ← Hf4Quad.low_eq hx]
  have h0 : x ≠ 0 := by linarith
  have h1 : x+1 ≠ 0 := by linarith
  have hq : x^2+8*x+1 ≠ 0 := by positivity
  unfold Hf4Quad.up Hf4Quad.low
  field_simp [h0,h1,hq]
  ring

theorem gap_ratio_cap {x : ℝ} (hx : 1 ≤ x) : (9*x+5)/(x^2+8*x+1) ≤ 2 := by
  apply (div_le_iff₀ (by positivity : 0 < x^2+8*x+1)).mpr
  nlinarith only [sq_nonneg x,hx]

theorem gap_cap {x a b c : ℝ} (hx : 1 ≤ x)
    (ha : (x-1)/x ≤ a) (hb : (x-1)/(x+1) ≤ b) (hc : x-1 ≤ c) :
    RemainingHf.basicUpper x-RemainingHf.basicLower x ≤ (1/105:ℝ)*a^2*b^4*c^2*2 := by
  have hx0 : 0 < x := by linarith
  have hm : 0 ≤ x-1 := by linarith
  have hn1 : 0 ≤ (x-1)/x := by positivity
  have hn2 : 0 ≤ (x-1)/(x+1) := by positivity
  have hn3 : 0 ≤ (9*x+5)/(x^2+8*x+1) := by positivity
  have ha0 := hn1.trans ha
  have hb0 := hn2.trans hb
  have hc0 := hm.trans hc
  rw [gap_factor hx]
  have hd := gap_ratio_cap hx
  gcongr

theorem gap_big {x : ℝ} (hx : x ∈ Icc 1 2) :
    RemainingHf.basicUpper x-RemainingHf.basicLower x ≤ (1/16000:ℝ) := by
  have hx0 : 0 < x := by linarith [hx.1]
  have h1 : (x-1)/x ≤ (1/2:ℝ) := (div_le_iff₀ hx0).mpr (by linarith [hx.2])
  have h2 : (x-1)/(x+1) ≤ (1/3:ℝ) := (div_le_iff₀ (by positivity)).mpr (by linarith [hx.2])
  have h := gap_cap hx.1 h1 h2 (by linarith [hx.2] : x-1 ≤ 1)
  norm_num at h
  linarith only [h]

theorem gap_small {x : ℝ} (hx : x ∈ Icc 1 (3/2)) :
    RemainingHf.basicUpper x-RemainingHf.basicLower x ≤ (1/1000000:ℝ) := by
  have hx0 : 0 < x := by linarith [hx.1]
  have h1 : (x-1)/x ≤ (1/3:ℝ) := (div_le_iff₀ hx0).mpr (by linarith [hx.2])
  have h2 : (x-1)/(x+1) ≤ (1/5:ℝ) := (div_le_iff₀ (by positivity)).mpr (by linarith [hx.2])
  have h := gap_cap hx.1 h1 h2 (by linarith [hx.2] : x-1 ≤ 1/2)
  norm_num at h
  linarith only [h]

theorem log_error_big {x : ℝ} (hx : x ∈ Icc 1 2) :
    log x ≤ RemainingHf.basicLower x+(1/16000:ℝ) := by
  linarith only [gap_big hx,RemainingHf.le_basicUpper hx.1]

theorem log_error_small {x : ℝ} (hx : x ∈ Icc 1 (3/2)) :
    log x-RemainingHf.basicLower x ≤ (1/1000000:ℝ) ∧
    RemainingHf.basicUpper x-log x ≤ (1/1000000:ℝ) := by
  constructor <;> linarith only [gap_small hx,RemainingHf.le_basicUpper hx.1,RemainingHf.basicLower_le hx.1]

theorem split_errors {x : ℝ} (hx : x ∈ Icc 1 2) :
    log x-RemainingHf.splitLower x ≤ (1/500000:ℝ) ∧
    RemainingHf.splitUpper x-log x ≤ (1/500000:ℝ) := by
  have hf := Wu04FactorEnvelopes.factors hx.1
  have hl : Wu04FactorEnvelopes.leftFactor x ≤ (3/2:ℝ) := by
    unfold Wu04FactorEnvelopes.leftFactor
    linarith [hx.2]
  have hr : Wu04FactorEnvelopes.rightFactor x ≤ (3/2:ℝ) := by
    unfold Wu04FactorEnvelopes.rightFactor
    apply (div_le_iff₀ (by linarith [hx.1] : 0 < 1+x)).mpr
    linarith [hx.2]
  have h1 := log_error_small ⟨hf.1,hl⟩
  have h2 := log_error_small ⟨hf.2.1,hr⟩
  rw [Wu04FactorEnvelopes.exact_log hx.1]
  unfold RemainingHf.splitLower RemainingHf.splitUpper
  constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2]

end Hf4Actual
