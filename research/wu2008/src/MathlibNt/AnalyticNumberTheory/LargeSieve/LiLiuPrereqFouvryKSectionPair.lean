import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKSectionReindex

/-!
# Both cutoff intervals in an actual IV.3 pair

The common-k diagonal is reindexed without identifying distinct original
tuples. Its interval is the intersection of the two separately reconstructed
carriers, hence includes both paid floor cutoffs. No cancellation is claimed.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- A single, completely explicit coprimality obstruction. In particular
it is not an arbitrary additional mask on an interval. -/
theorem wKSectionCoprime_iff (K : WExtractedKey) (a : ℤ) (r n₁ s k : ℕ) :
    wKSectionCoprime K a r n₁ s k ↔
      k.Coprime (K.1.2.2.1 * (K.1.2.2.2.2 * (r * s)) *
        a.natAbs * (K.1.1 * K.1.2.1 * n₁)) := by
  rw [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  constructor
  · rintro ⟨hδ, hr, ha, hn⟩
    exact ⟨⟨⟨hδ, hr⟩, ha.symm⟩, hn.symm⟩
  · rintro ⟨⟨⟨hδ, hr⟩, ha⟩, hn⟩
    exact ⟨hδ, hr, ha.symm, hn.symm⟩

/-- The paired domain has the maximum of the two lower endpoints.
All fixed tests and both explicit arithmetic masks remain visible. -/
theorem wKSectionCarrier_inter
    (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ) (K : WExtractedKey)
    (r n₁ n₂ n₂' s s' : ℕ) (h h' : ℤ) (b : ℕ)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) :
    wKSectionCarrier N a x η R S M Z K r n₁ n₂ s h b j cap positive c ∩
      wKSectionCarrier N a x η R S M Z K r n₁ n₂' s' h' b j cap positive c =
    (Icc (max (wKSectionGridLower M Z K r s h j)
        (wKSectionGridLower M Z K r s' h' j))
      (wKSectionGridUpper R S K j cap)).filter (fun k =>
        (wKSectionFixedSupport N a x η R S K r n₁ n₂ s ∧
          2 ^ b ≤ h.natAbs ∧ h.natAbs < 2 ^ (b + 1) ∧
          wKSectionFixedGrid x N S r n₁ n₂ s h j cap positive c ∧
          wKSectionCoprime K a r n₁ s k) ∧
        (wKSectionFixedSupport N a x η R S K r n₁ n₂' s' ∧
          2 ^ b ≤ h'.natAbs ∧ h'.natAbs < 2 ^ (b + 1) ∧
          wKSectionFixedGrid x N S r n₁ n₂' s' h' j cap positive c ∧
          wKSectionCoprime K a r n₁ s' k)) := by
  ext k
  simp only [wKSectionCarrier, mem_inter, mem_filter, mem_Icc, max_le_iff]
  constructor
  · rintro ⟨⟨⟨hl, hu⟩, hp⟩, ⟨⟨hl', _⟩, hp'⟩⟩
    exact ⟨⟨⟨hl, hl'⟩, hu⟩, hp, hp'⟩
  · rintro ⟨⟨⟨hl, hl'⟩, hu⟩, hp, hp'⟩
    exact ⟨⟨⟨hl, hu⟩, hp⟩, ⟨⟨hl', hu⟩, hp'⟩⟩

/-- The inner weight, including any beta-clean mask, is constant along
the section. The arbitrary first-modulus coefficient is not included. -/
theorem wKSectionTuple_innerWeight
    {K : WExtractedKey} {r n₁ n₂ s k : ℕ}
    (hf : wKSectionFixedCanonical K r n₁ n₂ s) (hk : 0 < k)
    (hkδ : k.Coprime K.1.2.2.1)
    (hkr : k.Coprime (K.1.2.2.2.2 * (r * s)))
    (he : K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2)
    (h : ℤ) (β ζ : ℕ → ℝ) :
    wCorrelationInnerWeight K β ζ (wKSectionTuple K r n₁ n₂ s h k) =
      ζ (wKSectionDeltaPrime K * s) * β (K.1.1 * n₂) := by
  unfold wCorrelationInnerWeight
  rw [wKSectionTuple_canonical hf hk hkδ hkr he h]
  rfl

/-- Exact common-k paired sum on the real cell and prefix. The weight
`F` can be the full IV.3 Gram kernel, with the small-root product intact. -/
theorem sum_wKSectionSlice_pair
    {A : Type*} [AddCommMonoid A]
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z)
    {K : WExtractedKey} {r n₁ n₂ n₂' s s' : ℕ} {h h' : ℤ} {b : ℕ}
    (hf : wKSectionFixedCanonical K r n₁ n₂ s)
    (hf' : wKSectionFixedCanonical K r n₁ n₂' s')
    (hΔ : 0 < K.2) (hΔ' : 0 < wKSectionDeltaPrime K)
    (he : K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ))
    (F : (WExtractedTuple × ℤ) → (WExtractedTuple × ℤ) → A) :
    let U := wCoprimeFiber x N S
      (wAnalyticPrefix (wAnalyticDyadicBlock
        (wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
          (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) cap) c
    (∑ t ∈ wKSectionSlice U r n₁ n₂ s h,
      ∑ u ∈ wKSectionSlice U r n₁ n₂' s' h',
        if (wGCDTuple (wExtractedOriginal t.1)).k₁ =
            (wGCDTuple (wExtractedOriginal u.1)).k₁ then F t u else 0) =
    ∑ k ∈ wKSectionCarrier N a x η R S M Z K r n₁ n₂ s h b j cap positive c ∩
      wKSectionCarrier N a x η R S M Z K r n₁ n₂' s' h' b j cap positive c,
      F (wKSectionTuple K r n₁ n₂ s h k) (wKSectionTuple K r n₁ n₂' s' h' k) := by
  dsimp only
  let C := wKSectionCarrier N a x η R S M Z K r n₁ n₂ s h b j cap positive c
  let C' := wKSectionCarrier N a x η R S M Z K r n₁ n₂' s' h' b j cap positive c
  have hcoord {n₂ s : ℕ} {h : ℤ}
      (hf : wKSectionFixedCanonical K r n₁ n₂ s) {k : ℕ}
      (hk : k ∈ wKSectionCarrier N a x η R S M Z K r n₁ n₂ s h b j cap positive c) :
      (wGCDTuple (wExtractedOriginal (wKSectionTuple K r n₁ n₂ s h k).1)).k₁ = k := by
    have ht := (wKSectionTuple_mem_filtered_iff hN hR hS hM hZ hf hΔ hΔ' he
      j cap positive c).mpr hk
    have hb := (mem_filter.mp (mem_filter.mp (mem_filter.mp ht).1).1).1
    rw [wKSectionTuple_canonical_of_mem hN (fun _ hq => (mem_Ioc.mp hq).1)
      hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hb]
    rfl
  calc
    _ = ∑ k ∈ C, ∑ l ∈ C',
        if k = l then F (wKSectionTuple K r n₁ n₂ s h k)
          (wKSectionTuple K r n₁ n₂' s' h' l) else 0 := by
      rw [sum_wKSectionSlice hN hR hS hM hZ hf hΔ hΔ' he j cap positive c]
      apply sum_congr rfl
      intro k hk
      rw [sum_wKSectionSlice hN hR hS hM hZ hf' hΔ hΔ' he j cap positive c]
      apply sum_congr rfl
      intro l hl
      rw [hcoord hf hk, hcoord hf' hl]
    _ = _ := by
      simp only [sum_ite_eq]
      rw [← sum_filter]
      apply sum_congr
      · ext k
        simp only [mem_filter, mem_inter, C, C']
      · intro k _
        rfl

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
