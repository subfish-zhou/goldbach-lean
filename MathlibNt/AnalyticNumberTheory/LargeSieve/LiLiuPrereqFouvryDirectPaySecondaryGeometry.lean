import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPaySecondaryEnergy

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The beta coordinate is n₁, not silently T. -/
theorem directPaySecondary_n_bound
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    (hQ : ∀ q ∈ Q, 0 < q) {T : ℝ} (hNT : ∀ n ∈ N, (n : ℝ) ≤ 2 * T)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock (wExtractedKeyFiber H N Q a P R S ξ b K) j positive) :
    (2 : ℝ) ^ j 2 ≤ 2 * T := by
  have hf := (mem_filter.mp ht).1
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp hf).1).1).1
  have hv := (wExtractedOriginal_valid hN hQ hz).1
  have hm := mem_wFactorExtractionTuples_iff.mp hz
  have hnmem : (wExtractedOriginal t.1).2.1 ∈ N := hm.2.2.2.2.2.2.2.1
  have hd : (wGCDTuple (wExtractedOriginal t.1)).n₁ ∣ (wExtractedOriginal t.1).2.1 := by
    rw [hv.N₁_eq]
    exact dvd_mul_left _ _
  exact (wAnalyticDyadicBlock_bounds hN hQ ht 2).1.trans
    ((Nat.cast_le.mpr (Nat.le_of_dvd (hN _ hnmem) hd)).trans (hNT _ hnmem))


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
