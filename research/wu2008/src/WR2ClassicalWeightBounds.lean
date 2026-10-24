import WR2ClassicalLogRatioKernel

noncomputable section
namespace WuPaper.ClassicalLogRatio
open Real

/-- Reciprocal bounds control the weight and both derivatives on any positive subinterval. -/
theorem weight_bounds {t R Q : ℝ} (ht : 0 < t) (ht1 : 0 < 1-t)
    (hr : t⁻¹ ≤ R) (hq : (1-t)⁻¹ ≤ Q) :
    |weight t| ≤ R+Q ∧ |weightD1 t| ≤ R^2+Q^2 ∧
      |weightD2 t| ≤ 2*R^3+2*Q^3 := by
  have hr0 := (inv_pos.mpr ht).le
  have hq0 := (inv_pos.mpr ht1).le
  have hr2 := pow_le_pow_left₀ hr0 hr 2
  have hq2 := pow_le_pow_left₀ hq0 hq 2
  have hr3 := pow_le_pow_left₀ hr0 hr 3
  have hq3 := pow_le_pow_left₀ hq0 hq 3
  have hw : weight t = t⁻¹+(1-t)⁻¹ := by simp [weight,one_div]
  have hw1 : weightD1 t = -(t⁻¹)^2+((1-t)⁻¹)^2 := by
    simp [weightD1,div_eq_mul_inv,inv_pow]
  have hw2 : weightD2 t = 2*(t⁻¹)^3+2*((1-t)⁻¹)^3 := by
    simp [weightD2,div_eq_mul_inv,inv_pow]
  constructor
  · rw [hw,abs_of_nonneg (add_nonneg hr0 hq0)]
    exact add_le_add hr hq
  constructor
  · rw [hw1]
    apply abs_le.mpr
    constructor <;> nlinarith only [hr2,hq2,sq_nonneg R,sq_nonneg Q,sq_nonneg (t⁻¹),sq_nonneg ((1-t)⁻¹)]
  · rw [hw2,abs_of_nonneg (by positivity)]
    linarith only [hr3,hq3]

end WuPaper.ClassicalLogRatio
#print axioms WuPaper.ClassicalLogRatio.weight_bounds
