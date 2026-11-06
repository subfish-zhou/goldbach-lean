import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectNormalizationMonomials

/-!
# Square-root payment of both section-length contributions

The second term is kept even when span/q exceeds D'. No lower bound such
as H*s≥n is used. The local k is cancelled under the square root only
after multiplication by the original reciprocal amplitude.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Square-root frequency normalization, with the remaining local denominator. -/
theorem directNormalization_sqrt_frequency {A H B : ℝ}
    (hA : 0 < A) (hHB : H ≤ A * B) :
    A⁻¹ * Real.sqrt H ≤ Real.sqrt B / Real.sqrt A := by
  calc
    _ ≤ A⁻¹ * Real.sqrt (A * B) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHB) (inv_nonneg.mpr hA.le)
    _ = _ := by
      rw [Real.sqrt_mul hA.le]
      have hs := (Real.sqrt_pos.2 hA).ne'
      have hsq := Real.sq_sqrt hA.le
      field_simp
      rw [hsq]

/-- Two distinct section-length monomials after square-root normalization. -/
theorem directNormalization_sqrt_length
    {D Dprime k r s q span H B : ℝ}
    (hD : 0 < D) (hk : 0 < k) (hr : 0 < r) (hs : 0 < s) (hq : 0 < q)
    (hDp : 0 ≤ Dprime) (hspan : 0 ≤ span)
    (hH : H ≤ D * k * r * s * B) (hspanK : span ≤ 2 * k) :
    (D * k * r * s)⁻¹ * Real.sqrt H * Real.sqrt (Dprime + span / q) ≤
      Real.sqrt B * (Real.sqrt Dprime / Real.sqrt (D * k * r * s) +
        Real.sqrt 2 / Real.sqrt (D * r * s * q)) := by
  have hA : 0 < D * k * r * s := by positivity
  have hsum : Real.sqrt (Dprime + span / q) ≤
      Real.sqrt Dprime + Real.sqrt (2 * k / q) := by
    have hh := directNormalization_sqrt_three hDp (div_nonneg hspan hq.le) (le_refl (0 : ℝ))
    simp only [add_zero, Real.sqrt_zero] at hh
    exact hh.trans (add_le_add le_rfl
      (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hspanK hq.le)))
  calc
    _ ≤ (Real.sqrt B / Real.sqrt (D * k * r * s)) *
        (Real.sqrt Dprime + Real.sqrt (2 * k / q)) :=
      mul_le_mul (directNormalization_sqrt_frequency hA hH) hsum
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
      rw [Real.sqrt_div (by positivity : 0 ≤ 2 * k),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_mul (by positivity : 0 ≤ D * k * r),
        Real.sqrt_mul (by positivity : 0 ≤ D * k), Real.sqrt_mul hD.le,
        Real.sqrt_mul (by positivity : 0 ≤ D * r * s),
        Real.sqrt_mul (by positivity : 0 ≤ D * r), Real.sqrt_mul hD.le]
      have hkd := (Real.sqrt_pos.2 hk).ne'
      field_simp



end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
