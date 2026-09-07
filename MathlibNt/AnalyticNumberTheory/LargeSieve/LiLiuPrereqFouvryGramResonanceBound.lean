import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramResonanceCount

/-!
# Uniform local-scale count and coefficient payment on occupied zero labels

For a base `v`, put `P=h*n₂'*s'`, `A=|P|`, and `B=d₁*n₁+|P|`.
One constant depending only on epsilon bounds every actual fiber by
`C*A^(2*epsilon)*B^epsilon`. Coefficients are bounded only on their original
supports; no envelope on the enlarged divisor carrier is assumed.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wGramResonanceScale (K : WExtractedKey) (ε : ℝ) (v : WGramResonanceBase) : ℝ :=
  ((wGramResonanceProduct v).natAbs : ℝ) ^ (2 * ε) *
    ((K.1.2.1 * v.1.2 + (wGramResonanceProduct v).natAbs : ℕ) : ℝ) ^ ε

theorem wGramResonanceFiber_card_le_local_scales {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : Finset ℕ) (a : ℤ) (x η R S M Z T : ℝ) (K : WExtractedKey)
      (b : ℕ) (V : Finset (WExtractedTuple × ℤ)),
      (∀ n ∈ N, 0 < n) → a ≠ 0 → 0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      (∀ n ∈ N, T ≤ (n : ℝ)) → x ^ η < T →
      V ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
        (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K →
      ∀ v ∈ wGramResonanceBases (wGramZeroLabels K a V),
        ((wGramResonanceFiber (wGramZeroLabels K a V) v).card : ℝ) ≤
          C * wGramResonanceScale K ε v := by
  obtain ⟨C, hC, hbound⟩ := iv3_resonance_divisor_sum_le_local_scales hε
  refine ⟨C, hC, ?_⟩
  intro N a x η R S M Z T K b V hN ha hR hS hM hZ hNT hT hV v hv
  have hc : ((wGramResonanceFiber (wGramZeroLabels K a V) v).card : ℝ) ≤
      ∑ m ∈ (wGramResonanceProduct v).natAbs.divisors,
        (fouvryTau 2 ((wGramResonanceProduct v) *
          ((K.1.2.1 : ℤ) * v.1.2 - m)).natAbs : ℝ) := by
    exact_mod_cast wGramResonanceFiber_card_le_divisor_sum
      hN ha hR hS hM hZ hNT hT hV hv
  apply hc.trans
  simpa only [wGramResonanceScale, mul_assoc] using
    hbound K.1.2.1 v.1.2 (wGramResonanceProduct v)
      ((wGramResonanceProduct v).natAbs : ℝ)
      ((K.1.2.1 * v.1.2 + (wGramResonanceProduct v).natAbs : ℕ) : ℝ)
      (by positivity) (by positivity) le_rfl le_rfl

/-- The coefficient envelope is used only at the original beta indices in N
and original zeta indices in `(0,floor S]`, derived from occupied witnesses. -/
theorem wGramWeight_abs_le_of_support
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) {K : WExtractedKey} {b : ℕ}
    {V : Finset (WExtractedTuple × ℤ)}
    (hV : V ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K)
    (β ζ : ℕ → ℝ) {Bβ Bζ : ℝ} (hBβ : 0 ≤ Bβ) (hBζ : 0 ≤ Bζ)
    (hβ : ∀ n ∈ N, |β n| ≤ Bβ) (hζ : ∀ s ∈ Ioc 0 ⌊S⌋₊, |ζ s| ≤ Bζ)
    {L : WGramLabel} (hL : L ∈ wGramLabels V) :
    |wGramWeight K β ζ L| ≤ (Bβ * Bζ) ^ 2 := by
  obtain ⟨hf, hf', _, hΔ', _⟩ :=
    wGramLabels_eligible hN (fun _ hq => (mem_Ioc.mp hq).1) hV hL
  obtain ⟨hsup, hsup', _, _⟩ := wGramLabels_fixedSupport hN hR hS hM hZ hV hL
  have hb := hβ _ hsup.2.2.2.1
  have hb' := hβ _ hsup'.2.2.2.1
  have hz := hζ _ (mem_Ioc.mpr
    ⟨Nat.mul_pos hΔ' hf.2.2.2.2.2.2.1, hsup.2.1⟩)
  have hz' := hζ _ (mem_Ioc.mpr
    ⟨Nat.mul_pos hΔ' hf'.2.2.2.2.2.2.1, hsup'.2.1⟩)
  rw [wGramWeight, abs_mul, abs_mul, abs_mul]
  calc
    _ ≤ (Bζ * Bβ) * (Bζ * Bβ) :=
      mul_le_mul (mul_le_mul hz hb (abs_nonneg _) hBζ)
        (mul_le_mul hz' hb' (abs_nonneg _) hBζ)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hBζ hBβ)
    _ = _ := by ring

/-- Quantitative whole-zero-mass bound, with one epsilon constant before
every support, key, prefix, cell and coefficient sequence is chosen. -/
theorem wGramZeroLabels_sum_le_local_scales {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : Finset ℕ) (a : ℤ) (x η R S M Z T : ℝ) (K : WExtractedKey)
      (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ))
      (V : Finset (WExtractedTuple × ℤ)) (β ζ : ℕ → ℝ) (Bβ Bζ : ℝ),
      (∀ n ∈ N, 0 < n) → a ≠ 0 → 0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      (∀ n ∈ N, T ≤ (n : ℝ)) → x ^ η < T →
      V ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
        (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K →
      0 ≤ Bβ → 0 ≤ Bζ →
      (∀ n ∈ N, |β n| ≤ Bβ) → (∀ s ∈ Ioc 0 ⌊S⌋₊, |ζ s| ≤ Bζ) →
      (∑ L ∈ wGramZeroLabels K a V,
        |wGramWeight K β ζ L| *
          (wGramPairCount N a x η R S M Z K b j cap positive c L : ℝ)) ≤
        (Bβ * Bζ) ^ 2 * (2 ^ j 1 : ℕ) * C *
          ∑ v ∈ wGramResonanceBases (wGramZeroLabels K a V),
            wGramResonanceScale K ε v := by
  obtain ⟨C, hC, hcount⟩ := wGramResonanceFiber_card_le_local_scales hε
  refine ⟨C, hC, ?_⟩
  intro N a x η R S M Z T K b j cap positive c V β ζ Bβ Bζ
    hN ha hR hS hM hZ hNT hT hV hBβ hBζ hβ hζ
  rw [sum_wGramResonanceFiber, mul_sum]
  apply sum_le_sum
  intro v hv
  let E : ℝ := (Bβ * Bζ) ^ 2 * (2 ^ j 1 : ℕ)
  have hE : 0 ≤ E := mul_nonneg (sq_nonneg _) (by positivity)
  have hc := hcount N a x η R S M Z T K b V hN ha hR hS hM hZ hNT hT hV v hv
  calc
    _ ≤ ∑ _t ∈ wGramResonanceFiber (wGramZeroLabels K a V) v, E := by
      apply sum_le_sum
      intro t ht
      have hL := mem_wGramResonanceFiber.mp ht
      have hw := wGramWeight_abs_le_of_support hN hR hS hM hZ hV β ζ
        hBβ hBζ hβ hζ (mem_filter.mp hL).1
      have hk : (wGramPairCount N a x η R S M Z K b j cap positive c
          (wGramResonanceJoin v t) : ℝ) ≤ (2 ^ j 1 : ℕ) := by
        exact_mod_cast wGramPairCount_le_dyadic N a x η R S M Z K b j cap positive c
          (wGramResonanceJoin v t)
      exact mul_le_mul hw hk (by positivity) (sq_nonneg _)
    _ = E * (wGramResonanceFiber (wGramZeroLabels K a V) v).card := by
      simp only [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ E * (C * wGramResonanceScale K ε v) := mul_le_mul_of_nonneg_left hc hE
    _ = _ := by dsimp only [E]; ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
