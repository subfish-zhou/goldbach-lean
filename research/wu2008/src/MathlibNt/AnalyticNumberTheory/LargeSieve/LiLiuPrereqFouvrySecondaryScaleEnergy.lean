import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryScaleBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryGcdEnergy

/-!
# Summing the complete occupied secondary contribution

Both the divisor envelope and the ratio count are proved before use.
No fixed-data sum remains in the secondary term. The coarse powers below
still require comparison with the global C.2 scale; this is not (4.10).
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wGramSecondaryBases_weighted_sum_le_scale {δ : ℝ} (hδ : 0 < δ) :
    ∃ Cτ : ℝ, 0 < Cτ ∧
    ∀ (ε C : ℝ) (N : Finset ℕ) (F : ℕ) (a : ℤ) (x η R S M Z : ℝ)
      (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
      (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ) (Bβ Bζ : ℝ),
      0 ≤ ε → 0 ≤ C → (∀ n ∈ N, 0 < n) → (∀ n ∈ N, n ≤ F) →
      0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      0 ≤ Bβ → 0 ≤ Bζ →
      (∀ n ∈ N, |β n| ≤ Bβ) → (∀ s ∈ Ioc 0 ⌊S⌋₊, |ζ s| ≤ Bζ) →
      (∑ v ∈ wGramSecondaryBases (wGramSecondaryLabels K a (wCoprimeFiber x N S
          (wGramPrefix N a x η R S M Z K b j cap positive) c)),
        |wGramWeight K β ζ (wGramSecondaryJoin v 0)| *
          wGramSecondaryGcdDyadicMean ε C a R S K j cap v) ≤
        wGramSecondaryBaseCountBound K F j *
          ((Bβ * Bζ) ^ 2 * wGramSecondaryScaleEnvelope ε δ C Cτ a R S K F j cap) := by
  obtain ⟨Cτ, hCτ, hmean⟩ := wGramSecondaryBases_mean_le_scaleEnvelope hδ
  refine ⟨Cτ, hCτ, ?_⟩
  intro ε C N F a x η R S M Z K b j cap positive c β ζ Bβ Bζ
    hε hC hN hNF hR hS hM hZ hBβ hBζ hβ hζ
  let G := wGramSecondaryBases (wGramSecondaryLabels K a (wCoprimeFiber x N S
    (wGramPrefix N a x η R S M Z K b j cap positive) c))
  let E := (Bβ * Bζ) ^ 2 * wGramSecondaryScaleEnvelope ε δ C Cτ a R S K F j cap
  have hE : 0 ≤ E := mul_nonneg (sq_nonneg _)
    (wGramSecondaryScaleEnvelope_nonneg hC ε δ Cτ a R S K F j cap)
  have hw (v : WGramSecondaryBase) (hv : v ∈ G) :
      |wGramWeight K β ζ (wGramSecondaryJoin v 0)| ≤ (Bβ * Bζ) ^ 2 := by
    obtain ⟨L, hL, he⟩ := mem_image.mp hv
    rw [← he]
    exact wGramWeight_abs_le_of_support (L := L) hN hR hS hM hZ
      (wGramCoprimePrefix_subset N a x η R S M Z K b j cap positive c)
      β ζ hBβ hBζ hβ hζ (mem_filter.mp hL).1
  calc
    _ ≤ ∑ _v ∈ G, E := by
      apply sum_le_sum
      intro v hv
      exact mul_le_mul (hw v hv)
        (hmean ε C N F a x η R S M Z K b j cap positive c hε hC hN hNF hR hS hM hZ v hv)
        (wGramSecondaryGcdDyadicMean_nonneg hC ε a R S K j cap v) (sq_nonneg _)
    _ = (G.card : ℝ) * E := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (wGramSecondaryBases_card_le_ratio hN hNF hR hS hM hZ K b j cap positive c) hE

theorem wSeparatedCorrelationEnergy_secondary_paid {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ Czero Cnonzero Cτ : ℝ, 0 < Czero ∧ 0 < Cnonzero ∧ 0 < Cτ ∧
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
            wGramSecondaryScaleEnvelope κ δ Cnonzero Cτ a R S K F j cap) +
        ∑ L ∈ (wGramLabels (wCoprimeFiber x N S
            (wGramPrefix N a x η R S M Z K b j cap positive) c)).filter
              (fun L => wGramNumerator K a L ≠ 0 ∧ ¬ wGramSecondaryResonant L),
          |wGramWeight K β ζ L| *
            wGramFouvryCost κ Cnonzero a R S M Z K j cap L) := by
  obtain ⟨Czero, Cnonzero, hCzero, hCnonzero, henergy⟩ :=
    wSeparatedCorrelationEnergy_secondary_gcdMean hε hκ
  obtain ⟨Cτ, hCτ, hsecondary⟩ := wGramSecondaryBases_weighted_sum_le_scale hδ
  refine ⟨Czero, Cnonzero, Cτ, hCzero, hCnonzero, hCτ, ?_⟩
  intro N F a x η R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hNF hx hη hSupport hBβ hBζ hβ hζ
  have hN : ∀ n ∈ N, 0 < n := by
    intro n hn
    have hp := Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) εSupport
    exact_mod_cast hp.trans_le (hSupport.trans (hNT n hn))
  apply (henergy N F a x η R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hNF hx hη hSupport hBβ hBζ hβ hζ).trans
  apply add_le_add le_rfl
  apply add_le_add _ le_rfl
  exact hsecondary κ Cnonzero N F a x η R S M Z K b j cap positive c β ζ Bβ Bζ
    hκ.le hCnonzero.le hN hNF hR hS hM hZ hBβ hBζ hβ hζ

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
