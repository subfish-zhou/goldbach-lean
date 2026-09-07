import MathlibNt.SieveTheory.LiLiuPrereqWFEdgeDensity

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.G9ExtendedUpper
open JurkatRichert1965ChenGammaOneQOne
open EdgeDensity

theorem upper_bounded {s : ℝ} (hs : (1 / 2 : ℝ) ≤ s) (hs3 : s ≤ 3) :
    0 ≤ jr1965F s ∧ jr1965F s ≤ 2 * jr1965DelayConstant := by
  rw [jr1965F_eq_of_le_three hs3]
  have hM := CoordinateShift.delayConstant_pos
  unfold jr1965DelayConstant at hM ⊢
  have hs0 : 0 < s := by linarith
  constructor
  · positivity
  · apply (div_le_iff₀ hs0).mpr
    nlinarith

theorem small_dimension_scalar {ε L K C r s : ℝ}
    (hε : 0 < ε) (hε8 : ε < 1 / 8) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hKL : K ≤ L) (hC : 0 ≤ C)
    (hr : 0 ≤ r) (hr8 : r ≤ 8)
    (hs : (1 / 2 : ℝ) ≤ s) (hsc : s ≤ 2 * (1 + ε + ε ^ 9))
    (hid : jr1965F 2 * r = jr1965F s * (1 + ε + ε ^ 9)) :
    (jr1965F 2 + C * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
        L ^ (-(1 / 3 : ℝ)))) * r * (1 + 2 * K / L) ≤
      jr1965F s + (24 * C + 12 * jr1965DelayConstant) *
        (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * L ^ (-(1 / 3 : ℝ))) := by
  let A := (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * L ^ (-(1 / 3 : ℝ))
  let T := ε + A
  let M := jr1965DelayConstant
  have hM : 0 ≤ M := CoordinateShift.delayConstant_pos.le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hL0 : 0 < L := by linarith
  have ht0 : 0 ≤ K / L := div_nonneg hK hL0.le
  have ht1 : K / L ≤ 1 := (div_le_one hL0).mpr hKL
  have htA : K / L ≤ A := dimension_quotient_le_target hε (by linarith) hL hK
  have hc := CoordinateShift.scale_bounds hε hε8
  obtain ⟨hF, hFM⟩ := upper_bounded hs (by linarith [hc.2.2])
  change jr1965F s ≤ 2 * M at hFM
  have hmain : jr1965F 2 * r ≤ jr1965F s + 4 * M * ε := by
    rw [hid]
    have h := mul_le_mul_of_nonneg_left hc.2.1 hF
    have h' := mul_le_mul_of_nonneg_right hFM hε.le
    nlinarith
  have hmain2 : jr1965F 2 * r ≤ 4 * M := by
    rw [hid]
    have h := mul_le_mul_of_nonneg_left
      (show 1 + ε + ε ^ 9 ≤ 2 by linarith [hc.2.2]) hF
    nlinarith
  have hratio : r * (1 + 2 * K / L) ≤ 24 := by
    rw [mul_div_assoc]
    nlinarith
  have hpaid := mul_le_mul_of_nonneg_left htA (show 0 ≤ 8 * M by positivity)
  have hcross := mul_le_mul_of_nonneg_right hmain2 (show 0 ≤ 2 * (K / L) by positivity)
  have herr := mul_le_mul_of_nonneg_left hratio (mul_nonneg hC hT)
  change (jr1965F 2 + C * T) * r * (1 + 2 * K / L) ≤
    jr1965F s + (24 * C + 12 * M) * T
  rw [mul_div_assoc] at herr ⊢
  dsimp [T] at herr ⊢
  nlinarith [mul_nonneg hM hA, mul_nonneg hM hε.le]

theorem large_dimension_scalar {a ε x y K : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hx : 1 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ 4 * x) (hxK : x ≤ K) :
    (y / a * (1 + K / a)) ^ 2 ≤
      (16 * ((1 / a) * (1 + 1 / a)) ^ 2) *
        ((ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * x ^ (-(1 / 3 : ℝ))) := by
  have h := large_dimension_square_le_target ha hε hε1 hx
    (show 0 ≤ y / 4 by positivity) (show y / 4 ≤ x by linarith) hxK
  have h' := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 16 by norm_num)
  calc
    _ = 16 * (y / 4 / a * (1 + K / a)) ^ 2 := by ring
    _ ≤ _ := by simpa only [mul_assoc] using h'

#print axioms small_dimension_scalar
#print axioms large_dimension_scalar
end MathlibNt.SieveTheory.LiLiuPrereqWF.G9ExtendedUpper
