import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectJoinedTerms
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectNormalizationRoots

/-! 次级项的字面局部包络；长区间分式保留，未声称最终归一化。 -/
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- inclusive grid endpoint must be paid, not discarded. -/
theorem directPaySecondary_grid (R S : ℝ) (K : WExtractedKey)
    (j cap : Fin 5 → ℕ) :
    ((wKSectionGridUpper R S K j cap + 1 : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ j 1 := by
  have hu : wKSectionGridUpper R S K j cap ≤ 2 ^ (j 1 + 1) - 1 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hp : 0 < (2 : ℕ) ^ (j 1 + 1) := by positivity
  have hh : wKSectionGridUpper R S K j cap + 1 ≤ 2 ^ (j 1 + 1) := by omega
  have hr : ((wKSectionGridUpper R S K j cap + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (j 1 + 1) := by exact_mod_cast hh
  simpa only [pow_succ, mul_comm] using hr

/-- Actual ratio count is H s log(2H), with both independent beta supports. -/
theorem directPaySecondary_count (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ) :
    wGramSecondaryBaseCountBound K F j =
      8 * (2 : ℝ) ^ j 0 * (2 : ℝ) ^ j 2 * ((F / K.1.1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ j 4 * (1 + Real.log (2 * (2 : ℝ) ^ j 0)) := by
  unfold wGramSecondaryBaseCountBound
  push_cast
  rw [pow_succ (2 : ℝ) (j 0), mul_comm ((2 : ℝ) ^ j 0) 2]
  ring

/-- Both natural subtraction and the exact lower q=nrs² are respected. -/
theorem directPaySecondary_envelope
    {κ δ C Cτ : ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (a : ℤ) (R S : ℝ) (K : WExtractedKey) (F : ℕ) (j cap : Fin 5 → ℕ) :
    wGramSecondaryScaleEnvelope κ δ C Cτ a R S K F j cap ≤
      (C * (a.natAbs.divisors.card : ℝ) *
        ((K.D' : ℝ) + 2 * (2 : ℝ) ^ j 1 /
          ((2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 * (2 : ℝ) ^ j 4)) *
        (16 * (2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 *
          (2 : ℝ) ^ j 4) ^ (1 / 2 + κ : ℝ)) *
        (2 * (2 : ℝ) ^ j 3 * Real.sqrt
          (8 * (2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 4 * (2 : ℝ) ^ j 4 *
            (Cτ * (wGramSecondaryNumeratorMax a K F j : ℝ) ^ δ))) := by
  have hr : ((2 ^ (j 3 + 1) - 1 : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ j 3 := by
    have hh : ((2 ^ (j 3 + 1) - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (j 3 + 1) := by
      exact_mod_cast Nat.sub_le (2 ^ (j 3 + 1)) 1
    simpa only [pow_succ, mul_comm] using hh
  have hq : ((2 ^ (j 2 + 1) * (2 ^ (j 3 + 1) - 1) *
      2 ^ (j 4 + 1) * 2 ^ (j 4 + 1) : ℕ) : ℝ) ≤
      16 * (2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 * (2 : ℝ) ^ j 4 := by
    push_cast
    calc
      _ ≤ (2 : ℝ) ^ (j 2 + 1) * (2 * (2 : ℝ) ^ j 3) *
          (2 : ℝ) ^ (j 4 + 1) * (2 : ℝ) ^ (j 4 + 1) := by gcongr
      _ = _ := by simp only [pow_succ]; ring
  have hs : ((2 ^ (j 2 + 1) * 2 ^ (j 4 + 1) * 2 ^ (j 4 + 1) : ℕ) : ℝ) =
      8 * (2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 4 * (2 : ℝ) ^ j 4 := by
    push_cast; simp only [pow_succ]; ring
  unfold wGramSecondaryScaleEnvelope
  rw [hs]
  apply mul_le_mul
  · apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add le_rfl
      push_cast
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [Nat.cast_add, Nat.cast_one] using directPaySecondary_grid R S K j cap
    · exact Real.rpow_le_rpow (by positivity) hq (by linarith)
    · positivity
    · positivity
  · exact mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg _)
  · positivity
  · positivity

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
