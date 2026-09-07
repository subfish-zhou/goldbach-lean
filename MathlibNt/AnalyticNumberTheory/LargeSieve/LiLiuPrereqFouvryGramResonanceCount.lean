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

def wGramResonanceDivisorMass (K : WExtractedKey) (β ζ : ℕ → ℝ)
    (v : WGramResonanceBase) : ℝ :=
  ∑ m ∈ (wGramResonanceProduct v).natAbs.divisors,
    ∑ s ∈ ((wGramResonanceProduct v) * ((K.1.2.1 : ℤ) * v.1.2 - m)).natAbs.divisors,
      |wGramWeight K β ζ (wGramResonanceJoin v (m, s, 0))|

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

/-- The weighted count retains the coordinate dependence of the coefficients;
it does not require any coefficient envelope. -/
theorem wGramResonanceFiber_weighted_le_divisor_mass
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ))
    (β ζ : ℕ → ℝ) {v : WGramResonanceBase}
    (hv : v ∈ wGramResonanceBases (wGramZeroLabels K a V)) :
    (∑ t ∈ wGramResonanceFiber (wGramZeroLabels K a V) v,
      |wGramWeight K β ζ (wGramResonanceJoin v t)| *
        (wGramPairCount N a x η R S M Z K b j cap positive c
          (wGramResonanceJoin v t) : ℝ)) ≤
      (2 ^ j 1 : ℕ) * wGramResonanceDivisorMass K β ζ v := by
  obtain ⟨L, hL, rfl⟩ := mem_image.mp hv
  have hd := wGramZeroLabels_resonance_data hN hR hS hM hZ hNT hT hV hL
  have hcount := iv3_resonance_sum_le_divisor_sum ha hd.1 hd.2.1
    (wGramResonanceFiber (wGramZeroLabels K a V) (wGramResonanceBase L))
    (fun t ht => (wGramZeroLabels_resonance_data hN hR hS hM hZ hNT hT hV
      (mem_wGramResonanceFiber.mp ht)).2.2)
    (fun t => |wGramWeight K β ζ (wGramResonanceJoin (wGramResonanceBase L) t)| *
      (wGramPairCount N a x η R S M Z K b j cap positive c
        (wGramResonanceJoin (wGramResonanceBase L) t) : ℝ))
    (fun m s => (2 ^ j 1 : ℕ) *
      |wGramWeight K β ζ (wGramResonanceJoin (wGramResonanceBase L) (m, s, 0))|)
    (fun _ _ => mul_nonneg (by positivity) (abs_nonneg _)) ?_
  · simpa only [wGramResonanceDivisorMass, wGramResonanceProduct,
      wGramResonanceBase, mul_sum] using hcount
  · intro t _
    have hc : (wGramPairCount N a x η R S M Z K b j cap positive c
        (wGramResonanceJoin (wGramResonanceBase L) t) : ℝ) ≤ (2 ^ j 1 : ℕ) := by
      exact_mod_cast wGramPairCount_le_dyadic N a x η R S M Z K b j cap positive c
        (wGramResonanceJoin (wGramResonanceBase L) t)
    exact (mul_le_mul_of_nonneg_left hc (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- All actual zero labels are regrouped and paid by the proved weighted
divisor encoding. Every common-k multiplicity has already been counted. -/
theorem wGramZeroLabels_sum_le_divisor_mass
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ) :
    (∑ L ∈ wGramZeroLabels K a V,
      |wGramWeight K β ζ L| *
        (wGramPairCount N a x η R S M Z K b j cap positive c L : ℝ)) ≤
      (2 ^ j 1 : ℕ) *
        ∑ v ∈ wGramResonanceBases (wGramZeroLabels K a V),
          wGramResonanceDivisorMass K β ζ v := by
  rw [sum_wGramResonanceFiber, mul_sum]
  apply sum_le_sum
  intro v hv
  exact wGramResonanceFiber_weighted_le_divisor_mass hN ha hR hS hM hZ hNT hT hV
    j cap positive c β ζ hv

end Actual

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
