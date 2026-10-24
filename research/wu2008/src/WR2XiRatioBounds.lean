import WR2XiDenominatorBounds

/-! Endpoint bounds for the rational logarithm arguments in Xi2. -/
noncomputable section
namespace WuPaper.R2Xi

/-- An increasing affine quotient, with both endpoint denominators positive. -/
theorem affine_ratio_le {A B C D a t : ℝ} (hat : a ≤ t)
    (ha : 0 < C + D * a) (ht : 0 < C + D * t)
    (hdet : 0 ≤ B * C - A * D) :
    (A + B * a) / (C + D * a) ≤ (A + B * t) / (C + D * t) := by
  apply (div_le_div_iff₀ ha ht).mpr
  nlinarith [mul_nonneg hdet (sub_nonneg.mpr hat)]

/-- The reciprocal product used by the rectangular mother-region term. -/
theorem reciprocal_product_le {N a b c d : ℝ} (hN : 0 ≤ N)
    (hca : c ≤ a) (hdb : d ≤ b)
    (hc : 0 < c) (hd : 0 < d) : N / (a * b) ≤ N / (c * d) := by
  apply div_le_div_of_nonneg_left hN (mul_pos hc hd)
  exact mul_le_mul hca hdb hd.le (hc.le.trans hca)

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.affine_ratio_le
#print axioms WuPaper.R2Xi.reciprocal_product_le
