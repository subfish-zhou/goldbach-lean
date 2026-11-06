import Hf4QuadCompactKernelCore

/-! UNCOMPILED draft. Exact coordinate changes; no precision/budget adjustment. -/
noncomputable section
namespace Hf4Quad.DirectCoordinates

/-- Cancel the common projective denominator before applying the two envelopes. -/
theorem quotient_coordinates {n d : ℝ} (hd : d ≠ 0) :
    ((n/d-1)/(n/d+3) = (n-d)/(n+3*d)) ∧
    ((n/d-1)/(3*(n/d)+1) = (n-d)/(3*n+d)) := by
  have hn : n/d-1 = (n-d)/d := by field_simp [hd]
  have hl : n/d+3 = (n+3*d)/d := by field_simp [hd]
  have hr : 3*(n/d)+1 = (3*n+d)/d := by field_simp [hd]
  constructor
  · rw [hn, hl, div_div_div_cancel_right₀ hd]
  · rw [hn, hr, div_div_div_cancel_right₀ hd]

theorem zero_coordinates (t : ℝ) :
    ((((t+2)/3)-1)/(((t+2)/3)+3) = (t-1)/(t+11)) ∧
    ((((t+2)/3)-1)/(3*((t+2)/3)+1) = (t-1)/(3*(t+3))) := by
  have h := quotient_coordinates (n := t+2) (d := 3) (by norm_num)
  have hn : t+2-(3:ℝ) = t-1 := by ring
  have hl : t+2+3*(3:ℝ) = t+11 := by ring
  have hr : 3*(t+2)+(3:ℝ) = 3*(t+3) := by ring
  simpa only [hn, hl, hr] using h

theorem negative_coordinates {t : ℝ} (ht : 1 ≤ t) :
    (let x := (t+3)*(t+2)/(6*(t+1));
      ((x-1)/(x+3) = t*(t-1)/(t^2+23*t+24)) ∧
      ((x-1)/(3*x+1) = t*(t-1)/(3*(t^2+7*t+8)))) := by
  have hp : 0 < t+1 := by linarith only [ht]
  have hd : (6:ℝ)*(t+1) ≠ 0 := mul_ne_zero (by norm_num) hp.ne'
  have h := quotient_coordinates (n := (t+3)*(t+2)) hd
  have hn : (t+3)*(t+2)-6*(t+1) = t*(t-1) := by ring
  have hl : (t+3)*(t+2)+3*(6*(t+1)) = t^2+23*t+24 := by ring
  have hr : 3*((t+3)*(t+2))+6*(t+1) = 3*(t^2+7*t+8) := by ring
  simpa only [hn, hl, hr] using h

/-- The quadratic argument uses quotient_coordinates directly with
n=(t^2+18*t+21)*(t+2)^2 and d=90*(t+1)^2. Keeping these factored
polynomials beats expanding them in the measured graph census. -/
theorem quadratic_den_ne {t : ℝ} (ht : 1 ≤ t) :
    (90:ℝ)*(t+1)^2 ≠ 0 := by
  have hp : 0 < t+1 := by linarith only [ht]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hp.ne')

/-- Radical conjugate factors collapse before taking any inverse. -/
theorem radical_argument (t : ℝ) :
    (t+9-2*TerminalE.radical)*(5+TerminalE.radical) /
      ((t+9+2*TerminalE.radical)*(5-TerminalE.radical)) =
    (5*(t+3)+TerminalE.radical*(t-1)) /
      (5*(t+3)-TerminalE.radical*(t-1)) := by
  have hn : (t+9-2*TerminalE.radical)*(5+TerminalE.radical) =
      5*(t+3)+TerminalE.radical*(t-1) := by
    nlinarith only [TerminalE.radical_sq]
  have hd : (t+9+2*TerminalE.radical)*(5-TerminalE.radical) =
      5*(t+3)-TerminalE.radical*(t-1) := by
    nlinarith only [TerminalE.radical_sq]
  rw [hn, hd]

theorem conjugate_coordinates {a b : ℝ} (hd : a-b ≠ 0) :
    ((((a+b)/(a-b))-1)/(((a+b)/(a-b))+3) = b/(2*a-b)) ∧
    ((((a+b)/(a-b))-1)/(3*((a+b)/(a-b))+1) = b/(2*a+b)) := by
  have h := quotient_coordinates (n := a+b) hd
  have hn : a+b-(a-b) = 2*b := by ring
  have hl : a+b+3*(a-b) = 2*(2*a-b) := by ring
  have hr : 3*(a+b)+(a-b) = 2*(2*a+b) := by ring
  simpa only [hn, hl, hr, mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)] using h

theorem radical_den_ne {t : ℝ} (ht : 1 ≤ t) :
    5*(t+3)-TerminalE.radical*(t-1) ≠ 0 := by
  have h := mul_nonneg (by linarith only [TerminalE.radical_lt_four] :
      0 ≤ 5-TerminalE.radical) (sub_nonneg.mpr ht)
  nlinarith only [h]

end Hf4Quad.DirectCoordinates
