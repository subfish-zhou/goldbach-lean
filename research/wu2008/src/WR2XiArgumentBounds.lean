import WR2XiRatioBounds

/-! Endpoint comparisons for the literal Xi2 logarithm arguments. -/
noncomputable section
namespace WuPaper.R2Xi
open Real

/-- The increasing tail ratio in the J and gamma-eight pieces. -/
theorem tail_argument_mono {S k a t : ℝ} (hS : 0 < S) (hk : 1 < k)
    (hat : a ≤ t) (ht : t < S - 1) :
    (a + 1) / ((k - 1) * (S - 1 - a)) ≤
      (t + 1) / ((k - 1) * (S - 1 - t)) := by
  have haD : 0 < (k - 1) * (S - 1 - a) := mul_pos (by linarith) (by linarith)
  have htD : 0 < (k - 1) * (S - 1 - t) := mul_pos (by linarith) (by linarith)
  apply (div_le_div_iff₀ haD htD).mpr
  nlinarith [mul_nonneg (mul_nonneg (le_of_lt hS) (le_of_lt (sub_pos.mpr hk)))
    (sub_nonneg.mpr hat)]

/-- The increasing mixed ratio in the middle branch of gamma six. -/
theorem mixed_argument_mono {S k a t : ℝ} (hS : 0 < S) (hkS : k ≤ S)
    (hat : a ≤ t) (ha : 0 < k * S - S - k * a) (ht : 0 < k * S - S - k * t) :
    S * (S - 1 - a) / (k * S - S - k * a) ≤
      S * (S - 1 - t) / (k * S - S - k * t) := by
  have h := affine_ratio_le (A := S * (S - 1)) (B := -S)
    (C := k * S - S) (D := -k) hat
    (by nlinarith only [ha]) (by nlinarith only [ht])
    (by nlinarith [mul_nonneg hS.le (sub_nonneg.mpr hkS)])
  convert h using 1 <;> ring

/-- The increasing reciprocal ratio in the triangular mother-region piece. -/
theorem triangular_argument_mono {S k a t : ℝ} (hS : 0 ≤ S) (hk : 0 ≤ k)
    (hat : a ≤ t) (ht : 0 < k * S - S - k * t) :
    S / (k * S - S - k * a) ≤ S / (k * S - S - k * t) := by
  apply div_le_div_of_nonneg_left hS ht
  nlinarith [mul_nonneg hk (sub_nonneg.mpr hat)]

/-- The last logarithm decreases, so its lower argument is the panel's right endpoint. -/
theorem final_argument_lower {S t b : ℝ} (htb : t ≤ b) : S - 1 - b ≤ S - 1 - t := by
  linarith

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.tail_argument_mono
#print axioms WuPaper.R2Xi.mixed_argument_mono
#print axioms WuPaper.R2Xi.triangular_argument_mono
