import WR2ClassicalWeightBounds

noncomputable section
namespace WuPaper.ClassicalNinth
open Real Set ClassicalLogRatio

theorem second_bound {s t : ℝ} (hs : s ∈ Icc (3/11) (3/10))
    (ht : t ∈ Icc (3/25) (3/10)) : |kernelD2 (1-s) (-1) s 0 t| ≤ 1900 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have ht1 : 0 < 1-t := by linarith [ht.2]
  have hs0 : 0 < s := by linarith [hs.1]
  have hp0 : 0 < 1-s-t := by linarith [hs.2,ht.2]
  have hr : t⁻¹ ≤ 25/3 := by rw [← one_div]; apply (div_le_iff₀ ht0).mpr; linarith [ht.1]
  have hq : (1-t)⁻¹ ≤ 10/7 := by rw [← one_div]; apply (div_le_iff₀ ht1).mpr; linarith [ht.2]
  obtain ⟨hw0,hw1,hw2⟩ := weight_bounds ht0 ht1 hr hq
  have hW0 : |weight t| ≤ 10 := by linarith only [hw0]
  have hW1 : |weightD1 t| ≤ 72 := by norm_num at hw1; linarith only [hw1]
  have hW2 : |weightD2 t| ≤ 1164 := by norm_num at hw2; linarith only [hw2]
  have hp : (1-s-t)⁻¹ ≤ 5/2 := by rw [← one_div]; apply (div_le_iff₀ hp0).mpr; linarith [hs.2,ht.2]
  have hpi : 0 ≤ (1-s-t)⁻¹ := (inv_pos.mpr hp0).le
  have hp2 := pow_le_pow_left₀ hpi hp 2
  have hlog : logarithm (1-s) (-1) s 0 t = log ((1-s-t)/s) := by
    rw [log_div hp0.ne' hs0.ne']
    simp [logarithm,sub_eq_add_neg]
  have hratio1 : 1 ≤ (1-s-t)/s := (one_le_div hs0).mpr (by linarith [hs.2,ht.2])
  have hratio2 : (1-s-t)/s ≤ 9/4 := (div_le_iff₀ hs0).mpr (by linarith [hs.1,ht.1])
  have hL0 : |logarithm (1-s) (-1) s 0 t| ≤ 5/4 := by
    rw [hlog,abs_of_nonneg (log_nonneg hratio1)]
    exact (log_le_sub_one_of_pos (div_pos hp0 hs0)).trans (by linarith)
  have hL1 : |logD1 (1-s) (-1) s 0 t| ≤ 5/2 := by
    have he : logD1 (1-s) (-1) s 0 t = -(1-s-t)⁻¹ := by
      simp [logD1,div_eq_mul_inv,sub_eq_add_neg]
    rw [he,abs_neg,abs_of_nonneg hpi]
    exact hp
  have hL2 : |logD2 (1-s) (-1) s 0 t| ≤ 25/4 := by
    have he : logD2 (1-s) (-1) s 0 t = -((1-s-t)⁻¹)^2 := by
      simp [logD2,div_eq_mul_inv,sub_eq_add_neg,inv_pow]
    rw [he,abs_neg,abs_of_nonneg (sq_nonneg _)]
    norm_num at hp2
    simpa only [inv_pow] using hp2
  have h := second_derivative_bound hW0 hW1 hW2 hL0 hL1 hL2
  norm_num at h
  linarith only [h]

end WuPaper.ClassicalNinth
#print axioms WuPaper.ClassicalNinth.second_bound
