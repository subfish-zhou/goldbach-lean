import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramResonanceScaleBound

/-!
# Explicit local zero-resonance payment in the original full energy

There is no remaining occupied-base sum. The zero term is
`(Bbeta*Bzeta)^2 * Czero * Kwidth * Rwidth * N₁width * Hwidth * (F/d) * Swidth`
times `Amax^(2 epsilon) * Bmax^epsilon`, with exact dyadic widths and the
actual fixed frequency sign. The nonzero Fouvry sum is unchanged.

This is a local estimate, not the global C.2 normalization: nonzero primary
and secondary aggregation, outer L² summation and the epsilon ledger remain.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Both constants precede all support, key, dyadic, prefix, cell and
coefficient data. The only additional input is the upper beta support. -/
theorem wSeparatedCorrelationEnergy_resonance_scaleBox
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
        ∑ L ∈ (wGramLabels (wCoprimeFiber x N S
            (wGramPrefix N a x η R S M Z K b j cap positive) c)).filter
              (fun L => wGramNumerator K a L ≠ 0),
          |wGramWeight K β ζ L| *
            wGramFouvryCost κ Cnonzero a R S M Z K j cap L := by
  obtain ⟨Czero, Cnonzero, hCzero, hCnonzero, henergy⟩ :=
    wSeparatedCorrelationEnergy_resonance_local hε hκ
  refine ⟨Czero, Cnonzero, hCzero, hCnonzero, ?_⟩
  intro N F a x η R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hNF hx hη hSupport hBβ hBζ hβ hζ
  have hN : ∀ n ∈ N, 0 < n := by
    intro n hn
    have hp := Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) εSupport
    have hnreal := hp.trans_le (hSupport.trans (hNT n hn))
    exact_mod_cast hnreal
  have hs := wGramResonanceBases_sum_le_scaleBox (a := a) (x := x) (η := η)
    hN hNF hR hS hM hZ K b j cap positive c hε.le
  apply (henergy N a x η R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hx hη hSupport hBβ hBζ hβ hζ).trans
  apply add_le_add _ le_rfl
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (Bβ * Bζ) ^ 2 * (2 ^ j 1 : ℕ) * Czero by positivity)

/-- Concrete five-small exponent, with the local cardinal and both power
envelopes expanded in the original energy bound. No base sum survives. -/
theorem wSeparatedCorrelationEnergy_resonance_scale_half_support
    {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ Czero Cnonzero : ℝ, 0 < Czero ∧ 0 < Cnonzero ∧
    ∀ (N : Finset ℕ) (F : ℕ) (a : ℤ) (x R S M Z T εSupport : ℝ)
      (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
      (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ) (Bβ Bζ : ℝ),
      a ≠ 0 → 0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      (∀ n ∈ N, T ≤ (n : ℝ)) → (∀ n ∈ N, n ≤ F) →
      1 < x → 0 < εSupport → x ^ εSupport ≤ T →
      0 ≤ Bβ → 0 ≤ Bζ →
      (∀ n ∈ N, |β n| ≤ Bβ) → (∀ s ∈ Ioc 0 ⌊S⌋₊, |ζ s| ≤ Bζ) →
      wSeparatedCorrelationEnergy x N S
        (wGramPrefix N a x (εSupport / 2) R S M Z K b j cap positive) c K β ζ a ≤
        (Bβ * Bζ) ^ 2 * (2 ^ j 1 : ℕ) * Czero *
          (2 ^ j 3 * 2 ^ j 2 * 2 ^ j 0 * (F / K.1.1) * 2 ^ j 4 : ℕ) *
          (((2 ^ (j 0 + 1) * (F / K.1.1) * 2 ^ (j 4 + 1) : ℕ) : ℝ) ^ (2 * ε) *
            (((K.1.2.1 * 2 ^ (j 2 + 1) +
              2 ^ (j 0 + 1) * (F / K.1.1) * 2 ^ (j 4 + 1) : ℕ) : ℝ) ^ ε)) +
        ∑ L ∈ (wGramLabels (wCoprimeFiber x N S
            (wGramPrefix N a x (εSupport / 2) R S M Z K b j cap positive) c)).filter
              (fun L => wGramNumerator K a L ≠ 0),
          |wGramWeight K β ζ L| *
            wGramFouvryCost κ Cnonzero a R S M Z K j cap L := by
  obtain ⟨Czero, Cnonzero, hCzero, hCnonzero, henergy⟩ :=
    wSeparatedCorrelationEnergy_resonance_scaleBox hε hκ
  refine ⟨Czero, Cnonzero, hCzero, hCnonzero, ?_⟩
  intro N F a x R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hNF hx hSupportPos hSupport hBβ hBζ hβ hζ
  exact henergy N F a x (εSupport / 2) R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hNF hx (by linarith) hSupport hBβ hBζ hβ hζ

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
