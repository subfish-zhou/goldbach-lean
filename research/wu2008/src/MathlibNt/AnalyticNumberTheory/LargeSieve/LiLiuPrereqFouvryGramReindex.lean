import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKSectionGram

/-!
# Occupied labels for the entire separated Gram energy

A label retains the common `(r,n₁)` and both ordered triples `(n₂,s,h)`.
It forgets only the common `k`, which is summed inside its fiber.
Labels are images of actual tuple-pairs, not an unrestricted rectangular box.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

abbrev WGramLabel := (ℕ × ℕ) × (ℕ × ℕ × ℤ) × (ℕ × ℕ × ℤ)

def wGramLabel (t u : WExtractedTuple × ℤ) : WGramLabel :=
  ((t.1.1.2.1, (wGCDTuple (wExtractedOriginal t.1)).n₁),
    ((wGCDTuple (wExtractedOriginal t.1)).n₂, t.1.1.2.2, t.2),
    ((wGCDTuple (wExtractedOriginal u.1)).n₂, u.1.1.2.2, u.2))

def wGramPairs (V : Finset (WExtractedTuple × ℤ)) :
    Finset ((WExtractedTuple × ℤ) × (WExtractedTuple × ℤ)) :=
  (V ×ˢ V).filter (fun p => wCorrelationOuter p.1 = wCorrelationOuter p.2)

def wGramLabels (V : Finset (WExtractedTuple × ℤ)) : Finset WGramLabel :=
  (wGramPairs V).image (fun p => wGramLabel p.1 p.2)

def wGramPrefix (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ)
    (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool) :
    Finset (WExtractedTuple × ℤ) :=
  wAnalyticPrefix (wAnalyticDyadicBlock
    (wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K) j positive) cap

theorem wGramPrefix_subset (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ)
    (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool) :
    wGramPrefix N a x η R S M Z K b j cap positive ⊆
      wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
        (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K := by
  intro t ht
  exact (mem_filter.mp (mem_filter.mp ht).1).1

/-- The initial Gram expansion still counts every ordered original pair. -/
theorem sum_wGramPairs {A : Type*} [AddCommMonoid A]
    (V : Finset (WExtractedTuple × ℤ))
    (F : (WExtractedTuple × ℤ) → (WExtractedTuple × ℤ) → A) :
    (∑ o ∈ V.image wCorrelationOuter,
      ∑ t ∈ V.filter (fun t => wCorrelationOuter t = o),
        ∑ u ∈ V.filter (fun u => wCorrelationOuter u = o), F t u) =
      ∑ p ∈ wGramPairs V, F p.1 p.2 := by
  calc
    _ = ∑ t ∈ V,
        ∑ u ∈ V.filter (fun u => wCorrelationOuter u = wCorrelationOuter t),
          F t u := by
      symm
      calc
        _ = ∑ o ∈ V.image wCorrelationOuter,
            ∑ t ∈ V.filter (fun t => wCorrelationOuter t = o),
              ∑ u ∈ V.filter (fun u => wCorrelationOuter u = wCorrelationOuter t),
                F t u :=
          (sum_fiberwise_of_maps_to
            (fun t ht => mem_image.mpr ⟨t, ht, rfl⟩) _).symm
        _ = _ := by
          apply sum_congr rfl
          intro o _
          apply sum_congr rfl
          intro t ht
          rw [(mem_filter.mp ht).2]
    _ = _ := by
      simp only [wGramPairs, sum_filter, sum_product]
      apply sum_congr rfl
      intro t _
      apply sum_congr rfl
      intro u _
      simp only [eq_comm (a := wCorrelationOuter u)]

/-- Fiberwise regrouping forgets no `k` multiplicity. Each label fiber is
exactly the two original slices with their common-`k` test. -/
theorem sum_wGramLabels {A : Type*} [AddCommMonoid A]
    (V : Finset (WExtractedTuple × ℤ))
    (F : (WExtractedTuple × ℤ) → (WExtractedTuple × ℤ) → A) :
    (∑ p ∈ wGramPairs V, F p.1 p.2) =
      ∑ L ∈ wGramLabels V,
        ∑ t ∈ wKSectionSlice V L.1.1 L.1.2 L.2.1.1 L.2.1.2.1 L.2.1.2.2,
          ∑ u ∈ wKSectionSlice V L.1.1 L.1.2 L.2.2.1 L.2.2.2.1 L.2.2.2.2,
            if (wGCDTuple (wExtractedOriginal t.1)).k₁ =
                (wGCDTuple (wExtractedOriginal u.1)).k₁ then F t u else 0 := by
  rw [show (∑ p ∈ wGramPairs V, F p.1 p.2) =
      ∑ L ∈ wGramLabels V,
        ∑ p ∈ (wGramPairs V).filter (fun p => wGramLabel p.1 p.2 = L),
          F p.1 p.2 from
    (sum_fiberwise_of_maps_to
      (fun p hp => mem_image.mpr ⟨p, hp, rfl⟩) _).symm]
  apply sum_congr rfl
  intro L _
  simp only [wGramPairs, filter_filter, sum_filter, sum_product, wKSectionSlice]
  apply sum_congr rfl
  intro t _
  by_cases ht : t.1.1.2.1 = L.1.1 ∧
      (wGCDTuple (wExtractedOriginal t.1)).n₁ = L.1.2 ∧
      (wGCDTuple (wExtractedOriginal t.1)).n₂ = L.2.1.1 ∧
      t.1.1.2.2 = L.2.1.2.1 ∧ t.2 = L.2.1.2.2
  · rw [if_pos ht]
    apply sum_congr rfl
    intro u _
    simp only [wCorrelationOuter, wGramLabel, Prod.ext_iff]
    split_ifs <;> simp_all only [and_true, true_and, and_self] <;> tauto
  · rw [if_neg ht]
    apply sum_eq_zero
    intro u _
    simp only [wCorrelationOuter, wGramLabel, Prod.ext_iff]
    split_ifs with hp
    · exact False.elim (ht ⟨hp.2.1.1, hp.2.1.2, hp.2.2.1.1,
        hp.2.2.1.2.1, hp.2.2.1.2.2⟩)
    · rfl

/-- Both canonical sections and both Delta conditions are extracted from
actual witnesses for an occupied label. Empty label sets need no witness. -/
theorem wGramLabels_eligible
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {V : Finset (WExtractedTuple × ℤ)}
    (hV : V ⊆ wExtractedKeyFiber H N Q a P R S ξ b K)
    {L : WGramLabel} (hL : L ∈ wGramLabels V) :
    wKSectionFixedCanonical K L.1.1 L.1.2 L.2.1.1 L.2.1.2.1 ∧
    wKSectionFixedCanonical K L.1.1 L.1.2 L.2.2.1 L.2.2.2.1 ∧
    0 < K.2 ∧ 0 < wKSectionDeltaPrime K ∧
    K.2 * wKSectionDeltaPrime K = K.1.2.2.1 * K.1.2.2.2.2 := by
  obtain ⟨⟨t, u⟩, hp, rfl⟩ := mem_image.mp hL
  obtain ⟨htu, ho⟩ := mem_filter.mp hp
  obtain ⟨ht, hu⟩ := mem_product.mp htu
  have htdata := wExtractedKeyFiber_kSection_arithmetic hN hQ (hV ht)
  have hudata := wExtractedKeyFiber_kSection_arithmetic hN hQ (hV hu)
  have hr := congrArg (fun o : ℕ × ℕ × ℕ => o.2.1) ho
  have hn := congrArg (fun o : ℕ × ℕ × ℕ => o.2.2) ho
  dsimp only [wCorrelationOuter] at hr hn
  refine ⟨htdata.1, ?_, htdata.2.2.2.2⟩
  change wKSectionFixedCanonical K t.1.1.2.1
    (wGCDTuple (wExtractedOriginal t.1)).n₁
    (wGCDTuple (wExtractedOriginal u.1)).n₂ u.1.1.2.2
  rw [hr, hn]
  exact hudata.1

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
