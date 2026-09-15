import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramAggregate

/-!
# Quantitative full-energy bound with the zero numerator separated

The same epsilon-dependent constant works for every original cell, key,
signed dyadic block, prefix and pair of arbitrary real coefficient sequences.
Only occupied labels are tested for canonicality. The resonant branch pays
the actual shared-k count; individual cancellation is used on the other branch.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wGramFouvryCost (ε C : ℝ) (a : ℤ) (R S M Z : ℝ) (K : WExtractedKey)
    (j cap : Fin 5 → ℕ) (L : WGramLabel) : ℝ :=
  C * (a.natAbs.divisors.card : ℝ) *
    ((K.D' : ℝ) + (wGramSpan R S M Z K j cap L : ℝ) / (wGramModulus L : ℝ)) *
    Real.sqrt ((wGramModulus L).gcd (wGramNumerator K a L).natAbs) *
    (wGramModulus L : ℝ) ^ (1 / 2 + ε : ℝ)

/-- This is the real triangle step: signs survive until this inequality. -/
theorem wGramWeight_mul_re_le (K : WExtractedKey) (β ζ : ℕ → ℝ)
    (L : WGramLabel) (z : ℂ) :
    wGramWeight K β ζ L * z.re ≤ |wGramWeight K β ζ L| * ‖z‖ := by
  calc
    _ ≤ |wGramWeight K β ζ L * z.re| := le_abs_self _
    _ = |wGramWeight K β ζ L| * |z.re| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)

/-- An unconditional finite global estimate, beyond the original positivity
and domain hypotheses. The two sums are over actual occupied ordered labels,
not arbitrary canonical tuples. Zero numerators do not invoke Weil. -/
theorem wSeparatedCorrelationEnergy_fouvry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ) (K : WExtractedKey)
      (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
      (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ),
      (∀ n ∈ N, 0 < n) → a ≠ 0 → 0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      wSeparatedCorrelationEnergy x N S
        (wGramPrefix N a x η R S M Z K b j cap positive) c K β ζ a ≤
        (∑ L ∈ (wGramLabels (wCoprimeFiber x N S
            (wGramPrefix N a x η R S M Z K b j cap positive) c)).filter
              (fun L => wGramNumerator K a L = 0),
          |wGramWeight K β ζ L| *
            (wGramPairCount N a x η R S M Z K b j cap positive c L : ℝ)) +
        ∑ L ∈ (wGramLabels (wCoprimeFiber x N S
            (wGramPrefix N a x η R S M Z K b j cap positive) c)).filter
              (fun L => wGramNumerator K a L ≠ 0),
          |wGramWeight K β ζ L| * wGramFouvryCost ε C a R S M Z K j cap L := by
  obtain ⟨C, hC, hbound⟩ := wKSectionPairSum_fouvry hε
  refine ⟨C, hC, ?_⟩
  intro N a x η R S M Z K b j cap positive c β ζ hN ha hR hS hM hZ
  let U := wGramPrefix N a x η R S M Z K b j cap positive
  let V := wCoprimeFiber x N S U c
  let T := wGramLabels V
  have hV : V ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K :=
    fun _ ht => wGramPrefix_subset N a x η R S M Z K b j cap positive
      (mem_filter.mp ht).1
  rw [wSeparatedCorrelationEnergy_eq_gram hN hR hS hM hZ K b j cap positive c β ζ]
  calc
    _ ≤ ∑ L ∈ T, if wGramNumerator K a L = 0 then
          |wGramWeight K β ζ L| *
            (wGramPairCount N a x η R S M Z K b j cap positive c L : ℝ)
        else |wGramWeight K β ζ L| * wGramFouvryCost ε C a R S M Z K j cap L := by
      apply sum_le_sum
      intro L hL
      apply (wGramWeight_mul_re_le K β ζ L _).trans
      by_cases hl : wGramNumerator K a L = 0
      · rw [if_pos hl]
        exact mul_le_mul_of_nonneg_left
          (wGramPairSum_norm_le_count N a x η R S M Z K b j cap positive c L)
          (abs_nonneg _)
      · rw [if_neg hl]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        obtain ⟨hf, hf', hΔ, hΔ', he⟩ :=
          wGramLabels_eligible hN (fun _ hq => (mem_Ioc.mp hq).1) hV hL
        exact hbound N a x η R S M Z K L.1.1 L.1.2 L.2.1.1 L.2.2.1
          L.2.1.2.1 L.2.2.2.1 L.2.1.2.2 L.2.2.2.2 b j cap positive c
          hN ha hR hS hM hZ hf hf' hΔ hΔ' he
    _ = _ := by rw [sum_ite]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
