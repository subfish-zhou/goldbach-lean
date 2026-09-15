import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKSectionCancellation

/-!
# Returning individual cancellation to the original weighted Gram section

The inner weights are fixed along the reconstructed section. The equality
below retains both original tuple indices and the common-k condition until
the exact reindexing; it does not identify repeated beta coordinates.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- One weighted section of the original separated Gram sum is exactly
the proved cancellation sum times its two fixed signed coefficients. -/
theorem wKSectionSlice_weighted_pair_eq
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z)
    {K : WExtractedKey} {r n₁ n₂ n₂' s s' : ℕ} {h h' : ℤ} {b : ℕ}
    (hf : wKSectionFixedCanonical K r n₁ n₂ s)
    (hf' : wKSectionFixedCanonical K r n₁ n₂' s')
    (hΔ : 0 < K.2) (hΔ' : 0 < wKSectionDeltaPrime K)
    (he : K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ) :
    let U := wCoprimeFiber x N S
      (wAnalyticPrefix (wAnalyticDyadicBlock
        (wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
          (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) cap) c
    (∑ t ∈ wKSectionSlice U r n₁ n₂ s h,
      ∑ u ∈ wKSectionSlice U r n₁ n₂' s' h',
        if (wGCDTuple (wExtractedOriginal t.1)).k₁ =
            (wGCDTuple (wExtractedOriginal u.1)).k₁ then
          ((wCorrelationInnerWeight K β ζ t : ℂ) *
            star (wCorrelationInnerWeight K β ζ u : ℂ)) *
            (wExtractedArithmeticPhase a t.2 t.1 *
              star (wExtractedArithmeticPhase a u.2 u.1)) else 0) =
      ((ζ (wKSectionDeltaPrime K * s) * β (K.1.1 * n₂) : ℝ) : ℂ) *
        star ((ζ (wKSectionDeltaPrime K * s') * β (K.1.1 * n₂') : ℝ) : ℂ) *
        wKSectionPairSum N a x η R S M Z K r n₁ n₂ n₂' s s'
          h h' b j cap positive c := by
  dsimp only
  rw [sum_wKSectionSlice_pair hN hR hS hM hZ hf hf' hΔ hΔ' he j cap positive c]
  unfold wKSectionPairSum
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  let V := wAnalyticPrefix (wAnalyticDyadicBlock
    (wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) cap
  have hV : V ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K := by
    intro t ht
    exact (mem_filter.mp (mem_filter.mp ht).1).1
  have ht := (wKSectionTuple_mem_filtered_iff hN hR hS hM hZ hf hΔ hΔ' he
    j cap positive c).mpr (mem_inter.mp hk).1
  have hu := (wKSectionTuple_mem_filtered_iff hN hR hS hM hZ hf' hΔ hΔ' he
    j cap positive c).mpr (mem_inter.mp hk).2
  have hQ : ∀ q ∈ Ioc 0 ⌊R * S⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have htcan := wKSectionTuple_canonical_of_mem hN hQ hf.1 hf.2.1 hf.2.2.1
    hf.2.2.2.1 (hV (mem_filter.mp ht).1)
  have hucan := wKSectionTuple_canonical_of_mem hN hQ hf'.1 hf'.2.1 hf'.2.2.1
    hf'.2.2.2.1 (hV (mem_filter.mp hu).1)
  have hphase := wCoprimeFiber_arithmetic_correlation hN hQ hV ht hu
    (by rw [htcan, hucan]; rfl) rfl (by rw [htcan, hucan]; rfl)
  have hweight : wCorrelationInnerWeight K β ζ (wKSectionTuple K r n₁ n₂ s h k) =
      ζ (wKSectionDeltaPrime K * s) * β (K.1.1 * n₂) := by
    unfold wCorrelationInnerWeight
    rw [htcan]
    rfl
  have hweight' : wCorrelationInnerWeight K β ζ (wKSectionTuple K r n₁ n₂' s' h' k) =
      ζ (wKSectionDeltaPrime K * s') * β (K.1.1 * n₂') := by
    unfold wCorrelationInnerWeight
    rw [hucan]
    rfl
  rw [hweight, hweight']
  exact congrArg (fun z : ℂ =>
    ((ζ (wKSectionDeltaPrime K * s) * β (K.1.1 * n₂) : ℝ) : ℂ) *
      star ((ζ (wKSectionDeltaPrime K * s') * β (K.1.1 * n₂') : ℝ) : ℂ) * z) hphase

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
