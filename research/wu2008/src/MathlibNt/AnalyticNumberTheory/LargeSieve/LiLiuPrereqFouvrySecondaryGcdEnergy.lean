import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryGcdBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramResonanceScaleEnergy

/-!
# The refined secondary arithmetic mean in the complete original energy

Constants are selected before the varying residue, support and coefficients.
The secondary fixed-data sum and the primary nonzero sum remain explicit.
This is not the fully aggregated estimate (4.10).
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wSeparatedCorrelationEnergy_secondary_gcdMean
    {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ Czero Cnonzero : ℝ, 0 < Czero ∧ 0 < Cnonzero ∧
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
        ((∑ v ∈ wGramSecondaryBases (wGramSecondaryLabels K a (wCoprimeFiber x N S
            (wGramPrefix N a x η R S M Z K b j cap positive) c)),
          |wGramWeight K β ζ (wGramSecondaryJoin v 0)| *
            wGramSecondaryGcdDyadicMean κ Cnonzero a R S K j cap v) +
        ∑ L ∈ (wGramLabels (wCoprimeFiber x N S
            (wGramPrefix N a x η R S M Z K b j cap positive) c)).filter
              (fun L => wGramNumerator K a L ≠ 0 ∧ ¬ wGramSecondaryResonant L),
          |wGramWeight K β ζ L| *
            wGramFouvryCost κ Cnonzero a R S M Z K j cap L) := by
  obtain ⟨Czero, Cnonzero, hCzero, hCnonzero, henergy⟩ :=
    wSeparatedCorrelationEnergy_resonance_scaleBox hε hκ
  refine ⟨Czero, Cnonzero, hCzero, hCnonzero, ?_⟩
  intro N F a x η R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hNF hx hη hSupport hBβ hBζ hβ hζ
  have hN : ∀ n ∈ N, 0 < n := by
    intro n hn
    have hp := Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) εSupport
    exact_mod_cast hp.trans_le (hSupport.trans (hNT n hn))
  have he := henergy N F a x η R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hNF hx hη hSupport hBβ hBζ hβ hζ
  rw [sum_wGram_nonzero_split_secondary] at he
  apply he.trans
  apply add_le_add le_rfl
  apply add_le_add _ le_rfl
  exact wGramSecondaryLabels_weighted_cost_le_gcdMean hκ.le hCnonzero.le hN
    a x η R S M Z K b j cap positive c β ζ

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
