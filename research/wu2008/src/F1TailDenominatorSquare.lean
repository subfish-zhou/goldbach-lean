import TailWholeTargetBridge

namespace F1TailDenominatorPayment

theorem fixed_square_identity (p d a : ℝ) (hd : d ≠ 0) :
    p/d-2*a*p+a^2*p*d=(p/d)*(1-a*d)^2 := by
  field_simp
  ring

theorem fixed_affine_lower {p d : ℝ} (hp : 0 ≤ p) (hd : 0 < d) (a : ℝ) :
    2*a*p-a^2*p*d ≤ p/d := by
  have h := mul_nonneg (div_nonneg hp hd.le) (sq_nonneg (1-a*d))
  rw [← fixed_square_identity p d a hd.ne'] at h
  linarith only [h]

end F1TailDenominatorPayment
