import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectMainEnergy

/-! # Divisor-free explicit main contribution

In addition to the joint gcd mean, the remaining single completion factor
`tau(|a|)` is paid by its proved uniform subpower bound. The already paid
zero and secondary contributions are kept literally unchanged.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wGramDirectMainSubpowerFactor (κ δ C Ca : ℝ) (a : ℤ) (R S : ℝ)
    (K : WExtractedKey) (j cap : Fin 5 → ℕ) : ℝ :=
  C * (Ca * (a.natAbs : ℝ) ^ δ) *
    ((K.D' : ℝ) + ((wKSectionGridUpper R S K j cap + 1 : ℕ) : ℝ) /
      (2 ^ j 2 * 2 ^ j 3 * 2 ^ j 4 * 2 ^ j 4 : ℕ)) *
    (2 ^ (j 2 + 1) * (2 ^ (j 3 + 1) - 1) *
      2 ^ (j 4 + 1) * 2 ^ (j 4 + 1) : ℕ) ^ (1 / 2 + κ : ℝ)

theorem wGramDirectMainCostFactor_le_subpower {δ : ℝ} (hδ : 0 < δ) :
    ∃ Ca : ℝ, 0 < Ca ∧ ∀ (κ C : ℝ) (a : ℤ) (R S : ℝ)
      (K : WExtractedKey) (j cap : Fin 5 → ℕ), 0 ≤ C → a ≠ 0 →
      wGramDirectMainCostFactor κ C a R S K j cap ≤
        wGramDirectMainSubpowerFactor κ δ C Ca a R S K j cap := by
  obtain ⟨Ca, hCa, htau⟩ := fouvryTau_le_const_rpow (k := 2) (by decide) hδ
  refine ⟨Ca, hCa, ?_⟩
  intro κ C a R S K j cap hC ha
  have ht : (a.natAbs.divisors.card : ℝ) ≤ Ca * (a.natAbs : ℝ) ^ δ := by
    simpa only [fouvryTau_two] using htau a.natAbs
      (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr ha))
  unfold wGramDirectMainCostFactor wGramDirectMainSubpowerFactor
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hC) (by positivity))
    (by positivity)

/-- No main gcd, divisor, or label sum remains. All constants are selected
before every family, signed shift, key, prefix and scale. -/
theorem wSeparatedCorrelationEnergy_direct_main_subpower
    {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ Czero Cnonzero Csecondary Cτ Cjoint Ca : ℝ,
      0 < Czero ∧ 0 < Cnonzero ∧ 0 < Csecondary ∧ 0 < Cτ ∧ 0 < Cjoint ∧ 0 < Ca ∧
    ∀ (N : Finset ℕ) (F : ℕ) (a : ℤ) (x η R S M Z T εSupport : ℝ)
      (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
      (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ) (Bβ Bζ : ℝ),
      a ≠ 0 → 0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      (∀ n ∈ N, T ≤ (n : ℝ)) → (∀ n ∈ N, n ≤ F) →
      1 < x → η < εSupport → x ^ εSupport ≤ T →
      0 ≤ Bβ → 0 ≤ Bζ →
      (∀ n ∈ N, |β n| ≤ Bβ) → (∀ s ∈ Ioc 0 ⌊S⌋₊, |ζ s| ≤ Bζ) →
      wSeparatedCorrelationEnergy x N S
        (wGramPrefix N a x η R S M Z K b j cap positive) c K β ζ a ≤
        (Bβ * Bζ) ^ 2 * (2 ^ j 1 : ℕ) * Czero *
          (wGramResonanceScaleBoxCard K F j : ℝ) *
            wGramResonanceScaleEnvelope K F j ε +
        (wGramSecondaryBaseCountBound K F j *
          ((Bβ * Bζ) ^ 2 *
            wGramSecondaryScaleEnvelope κ δ Cnonzero Csecondary a R S K F j cap) +
        ((Bβ * Bζ) ^ 2 * wGramDirectMainSubpowerFactor κ δ Cnonzero Ca a R S K j cap) *
          wGramMainJointMean δ Cτ Cjoint a K F j) := by
  obtain ⟨Czero, Cnonzero, Csecondary, Cτ, Cjoint,
    hCzero, hCnonzero, hCsecondary, hCτ, hCjoint, henergy⟩ :=
      wSeparatedCorrelationEnergy_direct_main_paid hε hκ hδ
  obtain ⟨Ca, hCa, hfactor⟩ := wGramDirectMainCostFactor_le_subpower hδ
  refine ⟨Czero, Cnonzero, Csecondary, Cτ, Cjoint, Ca,
    hCzero, hCnonzero, hCsecondary, hCτ, hCjoint, hCa, ?_⟩
  intro N F a x η R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hNF hx hη hSupport hBβ hBζ hβ hζ
  apply (henergy N F a x η R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hNF hx hη hSupport hBβ hBζ hβ hζ).trans
  apply add_le_add le_rfl
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (hfactor κ Cnonzero a R S K j cap hCnonzero.le ha) (sq_nonneg _))
    (wGramMainJointMean_nonneg δ Cτ Cjoint a K F j)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
