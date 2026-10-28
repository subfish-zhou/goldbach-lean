import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramResonanceDomain

/-!
# Paying the actual occupied zero fibers by their divisor encoding

The divisor variables are `(n₂,s)`; cancellation determines the signed `h'`.
The coefficient-dependent majorant preserves both original beta/zeta factors.
The k payment is only `2^(j 1)`, obtained from the actual interval.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wGramResonanceProduct (v : WGramResonanceBase) : ℤ :=
  v.2.1 * v.2.2.1 * v.2.2.2


section Actual

variable {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
  {a : ℤ} (ha : a ≠ 0) {x η R S M Z T : ℝ}
  (hR : 0 ≤ R) (hS : 0 ≤ S) (hM : 0 < M) (hZ : 0 < Z)
  (hNT : ∀ n ∈ N, T ≤ (n : ℝ)) (hT : x ^ η < T)
  {K : WExtractedKey} {b : ℕ} {V : Finset (WExtractedTuple × ℤ)}
  (hV : V ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
    (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K)

include hN ha hR hS hM hZ hNT hT hV

/-- The genuine aggregate divisor count is instantiated on each occupied
resonance base, not on a new caller-supplied canonical carrier. -/
theorem wGramResonanceFiber_card_le_divisor_sum
    {v : WGramResonanceBase} (hv : v ∈ wGramResonanceBases (wGramZeroLabels K a V)) :
    (wGramResonanceFiber (wGramZeroLabels K a V) v).card ≤
      ∑ m ∈ (wGramResonanceProduct v).natAbs.divisors,
        fouvryTau 2 ((wGramResonanceProduct v) *
          ((K.1.2.1 : ℤ) * v.1.2 - m)).natAbs := by
  obtain ⟨L, hL, rfl⟩ := mem_image.mp hv
  have hd := wGramZeroLabels_resonance_data hN hR hS hM hZ hNT hT hV hL
  apply iv3_resonance_card_le_divisor_sum ha hd.1 hd.2.1
  intro t ht
  exact (wGramZeroLabels_resonance_data hN hR hS hM hZ hNT hT hV
    (mem_wGramResonanceFiber.mp ht)).2.2


end Actual

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
