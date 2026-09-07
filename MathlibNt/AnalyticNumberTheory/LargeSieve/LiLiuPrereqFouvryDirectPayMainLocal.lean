import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectJoinedTerms
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectNormalizationRoots

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The literal inclusive upper endpoint, not an interval assumption on a mask. -/
theorem directPayMain_span (R S : ℝ) (K : WExtractedKey) (j cap : Fin 5 → ℕ) :
    ((wKSectionGridUpper R S K j cap + 1 : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ j 1 := by
  have hu : wKSectionGridUpper R S K j cap ≤ 2 ^ (j 1 + 1) - 1 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hp : 0 < (2 : ℕ) ^ (j 1 + 1) := by positivity
  have hh : wKSectionGridUpper R S K j cap + 1 ≤ 2 ^ (j 1 + 1) := by omega
  have hh' : ((wKSectionGridUpper R S K j cap + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (j 1 + 1) := by exact_mod_cast hh
  simpa only [pow_succ, mul_comm] using hh'

/-- True upper modulus used by the main completion factor. -/
theorem directPayMain_modulus (j : Fin 5 → ℕ) :
    ((2 ^ (j 2 + 1) * (2 ^ (j 3 + 1) - 1) *
      2 ^ (j 4 + 1) * 2 ^ (j 4 + 1) : ℕ) : ℝ) ≤
      16 * (2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 3 * ((2 : ℝ) ^ j 4) ^ 2 := by
  have hh : (2 ^ (j 3 + 1) - 1 : ℕ) ≤ 2 ^ (j 3 + 1) := Nat.sub_le _ _
  have h := Nat.mul_le_mul_right (2 ^ (j 4 + 1))
    (Nat.mul_le_mul_right (2 ^ (j 4 + 1))
      (Nat.mul_le_mul_left (2 ^ (j 2 + 1)) hh))
  have hr : ((2 ^ (j 2 + 1) * (2 ^ (j 3 + 1) - 1) *
      2 ^ (j 4 + 1) * 2 ^ (j 4 + 1) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (j 2 + 1) * (2 : ℝ) ^ (j 3 + 1) *
      (2 : ℝ) ^ (j 4 + 1) * (2 : ℝ) ^ (j 4 + 1) := by exact_mod_cast h
  convert hr using 1
  simp only [pow_succ]
  ring

/-- Exact square-root arithmetic identity used for the actual joint mean. -/
theorem directPayMain_mean_identity {N m s H A B L : ℝ}
    (hN : 0 ≤ N) (_hm : 0 ≤ m) (_hs : 0 ≤ s) (_hH : 0 ≤ H)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hL : 0 ≤ L) :
    Real.sqrt (N * m^2 * s^2 * H^2 * (A * L)) *
      Real.sqrt ((N * m^2 * H^2) * (B * s^2 * L)) =
      N * m^2 * s^2 * H^2 * Real.sqrt (A * B) * L := by
  rw [← Real.sqrt_mul (by positivity)]
  have he : N * m^2 * s^2 * H^2 * (A * L) *
      (N * m^2 * H^2 * (B * s^2 * L)) =
      (N * m^2 * s^2 * H^2 * L)^2 * (A * B) := by ring
  rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

/-- No sum remains, and the genuine logarithm and arithmetic maximum remain explicit. -/
theorem directPayMain_mean_eq (δ Cτ Cjoint : ℝ) (a : ℤ) (K : WExtractedKey)
    (F : ℕ) (j : Fin 5 → ℕ) (hCτ : 0 ≤ Cτ) (hCjoint : 0 ≤ Cjoint) :
    wGramMainJointMean δ Cτ Cjoint a K F j =
      (2 ^ (j 3 + 1) - 1 : ℕ) *
      ((2 : ℝ) ^ (j 2 + 1) * (F / K.1.1 : ℕ)^2 *
        ((2 : ℝ) ^ (j 4 + 1))^2 * ((2 : ℝ)^j 0)^2 *
        Real.sqrt (Cτ * Cjoint) *
        (mainRestrictedMax a K.1.2.1 (2^(j 2+1)) (F/K.1.1)
          (2^(j 0+1)) (2^(j 4+1)) : ℝ)^δ *
        Real.sqrt (1 + Real.log ((2 : ℝ)^(j 4+1)))) := by
  have hs : 1 ≤ (2 : ℝ) ^ (j 4 + 1) := one_le_pow₀ (by norm_num)
  have hl : 0 ≤ 1 + Real.log ((2 : ℝ) ^ (j 4 + 1)) :=
    add_nonneg (by norm_num) (Real.log_nonneg hs)
  unfold wGramMainJointMean
  dsimp only
  push_cast
  rw [show Cjoint * ((2 : ℝ) ^ (j 4 + 1))^2 *
      (1 + Real.log ((2 : ℝ) ^ (j 4 + 1))) =
      (Cjoint * (1 + Real.log ((2 : ℝ) ^ (j 4 + 1)))) *
        ((2 : ℝ) ^ (j 4 + 1))^2 by ring]
  rw [directPayMain_mean_identity (by positivity) (by positivity) (by positivity)
    (by positivity) hCτ (mul_nonneg hCjoint hl) (by positivity)]
  rw [show Cτ * (Cjoint * (1 + Real.log ((2 : ℝ) ^ (j 4 + 1)))) =
    (Cτ * Cjoint) * (1 + Real.log ((2 : ℝ) ^ (j 4 + 1))) by ring,
    Real.sqrt_mul (mul_nonneg hCτ hCjoint)]
  ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
