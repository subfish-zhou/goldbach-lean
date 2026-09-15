import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramResonanceReindex

/-!
# Resonance hypotheses from actual occupied witnesses

Both fixed supports, both canonical tuples, and the nonzero signed frequency
are recovered from the original key fiber. The lower beta support excludes
both degenerate differences. The common-k payment stays at its local dyadic
width, not the full level.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wGramCoprimePrefix_subset
    (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ)
    (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
    (c : Finset (ℕ × ℕ)) :
    wCoprimeFiber x N S (wGramPrefix N a x η R S M Z K b j cap positive) c ⊆
      wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
        (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K := by
  intro t ht
  exact wGramPrefix_subset N a x η R S M Z K b j cap positive
    (mem_filter.mp ht).1

private theorem actual_support
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) {K : WExtractedKey} {b : ℕ}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) :
    wKSectionFixedSupport N a x η R S K t.1.1.2.1
      (wGCDTuple (wExtractedOriginal t.1)).n₁
      (wGCDTuple (wExtractedOriginal t.1)).n₂ t.1.1.2.2 ∧ t.2 ≠ 0 := by
  have hQ : ∀ q ∈ Ioc 0 ⌊R * S⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  obtain ⟨hf, _, _, _, hΔ, hΔ', he⟩ := wExtractedKeyFiber_kSection_arithmetic hN hQ ht
  have hre := wExtractedKeyFiber_kSection_reconstruct hN hQ ht
  have ht' := ht
  rw [← hre] at ht'
  have hs := (wKSectionTuple_mem_key_iff hN hR hS hM hZ hf hΔ hΔ' he).mp ht'
  refine ⟨hs.1, ?_⟩
  have hp : 0 < 2 ^ b := by positivity
  have hh := hp.trans_le hs.2.1
  exact Int.natAbs_ne_zero.mp hh.ne'

theorem wGramLabels_fixedSupport
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) {K : WExtractedKey} {b : ℕ}
    {V : Finset (WExtractedTuple × ℤ)}
    (hV : V ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K)
    {L : WGramLabel} (hL : L ∈ wGramLabels V) :
    wKSectionFixedSupport N a x η R S K L.1.1 L.1.2 L.2.1.1 L.2.1.2.1 ∧
    wKSectionFixedSupport N a x η R S K L.1.1 L.1.2 L.2.2.1 L.2.2.2.1 ∧
    L.2.1.2.2 ≠ 0 ∧ L.2.2.2.2 ≠ 0 := by
  obtain ⟨⟨t, u⟩, hp, rfl⟩ := mem_image.mp hL
  obtain ⟨htu, ho⟩ := mem_filter.mp hp
  obtain ⟨ht, hu⟩ := mem_product.mp htu
  have hs := actual_support hN hR hS hM hZ (hV ht)
  have hs' := actual_support hN hR hS hM hZ (hV hu)
  have hr := congrArg (fun o : ℕ × ℕ × ℕ => o.2.1) ho
  have hn := congrArg (fun o : ℕ × ℕ × ℕ => o.2.2) ho
  dsimp only [wCorrelationOuter] at hr hn
  refine ⟨hs.1, ?_, hs.2, hs'.2⟩
  change wKSectionFixedSupport N a x η R S K t.1.1.2.1
    (wGCDTuple (wExtractedOriginal t.1)).n₁
    (wGCDTuple (wExtractedOriginal u.1)).n₂ u.1.1.2.2
  rw [hr, hn]
  exact hs'.1

/-- All arithmetic inputs of the genuine divisor count, obtained from an
occupied zero label. Neither difference is a caller-supplied hypothesis. -/
theorem wGramZeroLabels_resonance_data
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z T : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z)
    (hNT : ∀ n ∈ N, T ≤ (n : ℝ)) (hT : x ^ η < T)
    {K : WExtractedKey} {b : ℕ} {V : Finset (WExtractedTuple × ℤ)}
    (hV : V ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K)
    {L : WGramLabel} (hL : L ∈ wGramZeroLabels K a V) :
    L.2.1.2.2 * L.2.2.1 * L.2.2.2.1 ≠ 0 ∧
    (K.1.2.1 : ℤ) * L.1.2 - L.2.2.1 ≠ 0 ∧
    0 < L.2.1.1 ∧ 0 < L.2.1.2.1 ∧
    (K.1.2.1 * L.1.2).Coprime L.2.1.1 ∧
    (K.1.2.1 : ℤ) * L.1.2 - L.2.1.1 ≠ 0 ∧
    wGramNumerator K a L = 0 := by
  obtain ⟨hL, hl⟩ := mem_filter.mp hL
  obtain ⟨hf, hf', _, _, _⟩ :=
    wGramLabels_eligible hN (fun _ hq => (mem_Ioc.mp hq).1) hV hL
  obtain ⟨hsup, hsup', hh, _⟩ := wGramLabels_fixedSupport hN hR hS hM hZ hV hL
  have hcoords {r n m s : ℕ} (h : wKSectionFixedCanonical K r n m s) :
      0 < m ∧ 0 < s ∧ (K.1.2.1 * n).Coprime m := by
    obtain ⟨_, _, _, _, _, _, hs, _, hm, _, _, _, _, _, hc, _⟩ := h
    exact ⟨hm, hs, hc⟩
  have hm' : (L.2.2.1 : ℤ) ≠ 0 := by exact_mod_cast (hcoords hf').1.ne'
  have hs' : (L.2.2.2.1 : ℤ) ≠ 0 := by exact_mod_cast (hcoords hf').2.1.ne'
  exact ⟨mul_ne_zero (mul_ne_zero hh hm') hs',
    wKSectionFixedSupport_resonance_difference_ne_zero hNT hT hf' hsup',
    (hcoords hf).1, (hcoords hf).2.1, (hcoords hf).2.2,
    wKSectionFixedSupport_resonance_difference_ne_zero hNT hT hf hsup, hl⟩

theorem wGramPairCount_le_dyadic
    (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ) (K : WExtractedKey)
    (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
    (c : Finset (ℕ × ℕ)) (L : WGramLabel) :
    wGramPairCount N a x η R S M Z K b j cap positive c L ≤ 2 ^ j 1 := by
  apply (wGramPairCount_le_interval N a x η R S M Z K b j cap positive c L).trans
  have hsub :
      Icc (max (wKSectionGridLower M Z K L.1.1 L.2.1.2.1 L.2.1.2.2 j)
          (wKSectionGridLower M Z K L.1.1 L.2.2.2.1 L.2.2.2.2 j))
        (wKSectionGridUpper R S K j cap) ⊆
      Icc (2 ^ j 1) (2 ^ (j 1 + 1) - 1) := by
    intro k hk
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hk
    apply mem_Icc.mpr
    constructor
    · exact (le_max_right _ _).trans ((le_max_left _ _).trans hlo)
    · exact hhi.trans ((min_le_right _ _).trans (min_le_right _ _))
  apply (card_le_card hsub).trans
  rw [Nat.card_Icc, pow_succ]
  have hp : 0 < 2 ^ j 1 := by positivity
  omega

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
