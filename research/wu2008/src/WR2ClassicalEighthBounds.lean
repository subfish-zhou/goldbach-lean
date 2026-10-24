import WR2ClassicalWeightBounds

noncomputable section
namespace WuPaper.ClassicalEighth
open Real Set ClassicalLogRatio

/-- A global bound on the original eighth integral's full interval. -/
theorem second_bound {t : ℝ} (ht : t ∈ Icc (3/40) (1/3)) :
    |kernelD2 2 (-3) 1 0 t| ≤ 6000 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have ht1 : 0 < 1-t := by linarith [ht.2]
  have hp0 : 0 < 2-3*t := by linarith [ht.2]
  have hr : t⁻¹ ≤ 40/3 := by rw [← one_div]; apply (div_le_iff₀ ht0).mpr; linarith [ht.1]
  have hq : (1-t)⁻¹ ≤ 3/2 := by rw [← one_div]; apply (div_le_iff₀ ht1).mpr; linarith [ht.2]
  obtain ⟨hw0,hw1,hw2⟩ := weight_bounds ht0 ht1 hr hq
  have hW0 : |weight t| ≤ 15 := by linarith only [hw0]
  have hW1 : |weightD1 t| ≤ 181 := by norm_num at hw1; linarith only [hw1]
  have hW2 : |weightD2 t| ≤ 4748 := by norm_num at hw2; linarith only [hw2]
  have hp : (2-3*t)⁻¹ ≤ 1 := by rw [← one_div]; apply (div_le_iff₀ hp0).mpr; linarith [ht.2]
  have hpi : 0 ≤ (2-3*t)⁻¹ := (inv_pos.mpr hp0).le
  have hp2 := pow_le_pow_left₀ hpi hp 2
  have hlog : logarithm 2 (-3) 1 0 t = log (2-3*t) := by
    simp [logarithm,sub_eq_add_neg]
  have hL0 : |logarithm 2 (-3) 1 0 t| ≤ 1 := by
    rw [hlog,abs_of_nonneg (log_nonneg (by linarith [ht.2]))]
    exact (log_le_sub_one_of_pos hp0).trans (by linarith)
  have hL1 : |logD1 2 (-3) 1 0 t| ≤ 3 := by
    have he : logD1 2 (-3) 1 0 t = -3*(2-3*t)⁻¹ := by
      simp [logD1,div_eq_mul_inv,sub_eq_add_neg]
    rw [he,abs_mul,abs_of_nonneg hpi]
    norm_num
    linarith only [hp]
  have hL2 : |logD2 2 (-3) 1 0 t| ≤ 9 := by
    have he : logD2 2 (-3) 1 0 t = -9*((2-3*t)⁻¹)^2 := by
      norm_num [logD2,div_eq_mul_inv,sub_eq_add_neg,inv_pow]
    rw [he,abs_mul,abs_of_nonneg (sq_nonneg ((2-3*t)⁻¹))]
    norm_num at hp2 ⊢
    exact hp2
  have h := second_derivative_bound hW0 hW1 hW2 hL0 hL1 hL2
  norm_num at h
  linarith only [h]

end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.second_bound
