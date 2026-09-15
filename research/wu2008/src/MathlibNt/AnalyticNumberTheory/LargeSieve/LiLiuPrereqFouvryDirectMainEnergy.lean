import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectMainCost

/-! # Original Gram energy with all three arithmetic branches paid

The left side is the original separated correlation energy on the actual
prefix and coprime cell. Zero and secondary envelopes are unchanged; the
main branch has no occupied-base, frequency, common-index or gcd sum.
This is a local theorem, not the global C.2 power normalization.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Fully summed original energy. The five constants depend only on the
three positive loss exponents, never on the subsequent data or coefficients. -/
theorem wSeparatedCorrelationEnergy_direct_main_paid
    {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ Czero Cnonzero Csecondary Cτ Cjoint : ℝ,
      0 < Czero ∧ 0 < Cnonzero ∧ 0 < Csecondary ∧ 0 < Cτ ∧ 0 < Cjoint ∧
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
        ((Bβ * Bζ) ^ 2 * wGramDirectMainCostFactor κ Cnonzero a R S K j cap) *
          wGramMainJointMean δ Cτ Cjoint a K F j) := by
  obtain ⟨Czero, Cnonzero, Csecondary, hCzero, hCnonzero, hCsecondary, henergy⟩ :=
    wSeparatedCorrelationEnergy_secondary_paid hε hκ hδ
  obtain ⟨Cτ, Cjoint, hCτ, hCjoint, hmain⟩ := wGramDirectMain_weighted_cost_sum hδ
  refine ⟨Czero, Cnonzero, Csecondary, Cτ, Cjoint,
    hCzero, hCnonzero, hCsecondary, hCτ, hCjoint, ?_⟩
  intro N F a x η R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hNF hx hη hSupport hBβ hBζ hβ hζ
  have hN : ∀ n ∈ N, 0 < n := by
    intro n hn
    have hp := Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) εSupport
    exact_mod_cast hp.trans_le (hSupport.trans (hNT n hn))
  have hgap : x ^ η < T := (Real.rpow_lt_rpow_of_exponent_lt hx hη).trans_le hSupport
  apply (henergy N F a x η R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hNF hx hη hSupport hBβ hBζ hβ hζ).trans
  apply add_le_add le_rfl
  apply add_le_add le_rfl
  exact hmain κ Cnonzero N F a x η R S M Z T K b j cap positive c β ζ Bβ Bζ
    hκ.le hCnonzero.le ha hN hNF hR hS hM hZ hNT hgap hBβ hBζ hβ hζ

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
