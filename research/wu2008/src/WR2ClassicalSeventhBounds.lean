import WR2ClassicalLogRatioKernel

noncomputable section
namespace WuPaper.ClassicalSeventh
open Real Set ClassicalLogRatio

theorem second_bound {t : ℝ} (ht : t ∈ Icc (1/4) (1/3)) :
    |kernelD2 1 (-2) 0 1 t| ≤ 900 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hq0 : 0 < 1-t := by linarith [ht.2]
  have hp0 : 0 < 1-2*t := by linarith [ht.2]
  have hr0 : 0 ≤ t⁻¹ := (inv_pos.mpr ht0).le
  have hr : t⁻¹ ≤ 4 := by rw [← one_div]; apply (div_le_iff₀ ht0).mpr; linarith [ht.1]
  have hq : (1-t)⁻¹ ≤ 3/2 := by rw [← one_div]; apply (div_le_iff₀ hq0).mpr; linarith [ht.2]
  have hp : (1-2*t)⁻¹ ≤ 3 := by rw [← one_div]; apply (div_le_iff₀ hp0).mpr; linarith [ht.2]
  have hqi : 0 ≤ (1-t)⁻¹ := (inv_pos.mpr hq0).le
  have hpi : 0 ≤ (1-2*t)⁻¹ := (inv_pos.mpr hp0).le
  have hr2 := pow_le_pow_left₀ hr0 hr 2
  have hq2 := pow_le_pow_left₀ hqi hq 2
  have hp2 := pow_le_pow_left₀ hpi hp 2
  have hr3 := pow_le_pow_left₀ hr0 hr 3
  have hq3 := pow_le_pow_left₀ hqi hq 3
  have hw : weight t = t⁻¹+(1-t)⁻¹ := by simp [weight,one_div]
  have hw1 : weightD1 t = -(t⁻¹)^2+((1-t)⁻¹)^2 := by
    simp [weightD1,div_eq_mul_inv,inv_pow]
  have hw2 : weightD2 t = 2*(t⁻¹)^3+2*((1-t)⁻¹)^3 := by
    simp [weightD2,div_eq_mul_inv,inv_pow]
  have hl1 : logD1 1 (-2) 0 1 t = -2*(1-2*t)⁻¹-t⁻¹ := by
    simp [logD1,div_eq_mul_inv]; ring
  have hl2 : logD2 1 (-2) 0 1 t = -4*((1-2*t)⁻¹)^2+(t⁻¹)^2 := by
    simp [logD2,div_eq_mul_inv,inv_pow]; ring
  have hlog : logarithm 1 (-2) 0 1 t = log ((1-2*t)/t) := by
    rw [log_div hp0.ne' ht0.ne']
    simp [logarithm]; congr 1
  have hratio1 : 1 ≤ (1-2*t)/t := (one_le_div ht0).mpr (by linarith [ht.2])
  have hratio2 : (1-2*t)/t ≤ 2 := (div_le_iff₀ ht0).mpr (by linarith [ht.1])
  have hL0 : |logarithm 1 (-2) 0 1 t| ≤ 1 := by
    rw [hlog,abs_of_nonneg (log_nonneg hratio1)]
    exact (log_le_sub_one_of_pos (div_pos hp0 ht0)).trans (by linarith)
  have hW0 : |weight t| ≤ 6 := by rw [hw]; apply abs_le.mpr; constructor <;> linarith
  have hW1 : |weightD1 t| ≤ 19 := by rw [hw1]; apply abs_le.mpr; constructor <;> nlinarith [sq_nonneg (t⁻¹),sq_nonneg ((1-t)⁻¹)]
  have hW2 : |weightD2 t| ≤ 135 := by
    rw [hw2]
    apply abs_le.mpr
    constructor <;> nlinarith [pow_nonneg hr0 3,pow_nonneg hqi 3]
  have hL1 : |logD1 1 (-2) 0 1 t| ≤ 10 := by rw [hl1]; apply abs_le.mpr; constructor <;> linarith
  have hL2 : |logD2 1 (-2) 0 1 t| ≤ 52 := by
    rw [hl2]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg ((1-2*t)⁻¹),sq_nonneg (t⁻¹)]
  have h := second_derivative_bound hW0 hW1 hW2 hL0 hL1 hL2
  norm_num at h
  linarith

end WuPaper.ClassicalSeventh
#print axioms WuPaper.ClassicalSeventh.second_bound
