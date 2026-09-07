import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramReindex

/-!
# Global occupied-section estimate for the separated Gram energy

The exact identity precedes the real triangle inequality. In particular no
absolute values are inserted into the original signed beta/zeta weights.
The zero-numerator branch uses the actual paired-carrier count, not Weil.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wGramWeight (K : WExtractedKey) (β ζ : ℕ → ℝ) (L : WGramLabel) : ℝ :=
  (ζ (wKSectionDeltaPrime K * L.2.1.2.1) * β (K.1.1 * L.2.1.1)) *
    (ζ (wKSectionDeltaPrime K * L.2.2.2.1) * β (K.1.1 * L.2.2.1))

def wGramModulus (L : WGramLabel) : ℕ :=
  L.1.2 * L.1.1 * L.2.1.2.1 * L.2.2.2.1

def wGramNumerator (K : WExtractedKey) (a : ℤ) (L : WGramLabel) : ℤ :=
  iv3CorrelationNumerator K.1.2.1 L.1.2 L.2.1.1 L.2.2.1
    L.2.1.2.1 L.2.2.2.1 a L.2.1.2.2 L.2.2.2.2

/-- Both paid floor cutoffs enter through the maximum of the two lower
endpoints, with their respective local scales unchanged. -/
def wGramSpan (R S M Z : ℝ) (K : WExtractedKey)
    (j cap : Fin 5 → ℕ) (L : WGramLabel) : ℕ :=
  wKSectionGridUpper R S K j cap -
    max (wKSectionGridLower M Z K L.1.1 L.2.1.2.1 L.2.1.2.2 j)
      (wKSectionGridLower M Z K L.1.1 L.2.2.2.1 L.2.2.2.2 j) + 1

def wGramPairSum (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ)
    (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
    (c : Finset (ℕ × ℕ)) (L : WGramLabel) : ℂ :=
  wKSectionPairSum N a x η R S M Z K L.1.1 L.1.2 L.2.1.1 L.2.2.1
    L.2.1.2.1 L.2.2.2.1 L.2.1.2.2 L.2.2.2.2 b j cap positive c

def wGramPairCount (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ)
    (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
    (c : Finset (ℕ × ℕ)) (L : WGramLabel) : ℕ :=
  (wKSectionCarrier N a x η R S M Z K L.1.1 L.1.2 L.2.1.1
      L.2.1.2.1 L.2.1.2.2 b j cap positive c ∩
    wKSectionCarrier N a x η R S M Z K L.1.1 L.1.2 L.2.2.1
      L.2.2.2.1 L.2.2.2.2 b j cap positive c).card

theorem wGramPairSum_norm_le_count (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ)
    (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
    (c : Finset (ℕ × ℕ)) (L : WGramLabel) :
    ‖wGramPairSum N a x η R S M Z K b j cap positive c L‖ ≤
      (wGramPairCount N a x η R S M Z K b j cap positive c L : ℝ) := by
  unfold wGramPairSum wKSectionPairSum wGramPairCount
  apply (norm_sum_le _ _).trans
  simp only [norm_mul, norm_star, norm_wActualSmallRootFactor,
    norm_wActualReciprocalCorrelation, mul_one, sum_const, nsmul_eq_mul, le_refl]

/-- The zero-branch count is bounded by the cardinal of the actual
intersection interval, which is zero if the upper endpoint is too small. -/
theorem wGramPairCount_le_interval (N : Finset ℕ) (a : ℤ) (x η R S M Z : ℝ)
    (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
    (c : Finset (ℕ × ℕ)) (L : WGramLabel) :
    wGramPairCount N a x η R S M Z K b j cap positive c L ≤
      (Icc (max (wKSectionGridLower M Z K L.1.1 L.2.1.2.1 L.2.1.2.2 j)
          (wKSectionGridLower M Z K L.1.1 L.2.2.2.1 L.2.2.2.2 j))
        (wKSectionGridUpper R S K j cap)).card := by
  unfold wGramPairCount
  rw [wKSectionCarrier_inter]
  exact card_filter_le _ _

/-- Exact global reindexing of the previously defined energy. Eligibility
is proved only for occupied labels; no canonicality premise is imposed on
arbitrary labels, and the empty-carrier case is automatic. -/
theorem wSeparatedCorrelationEnergy_eq_gram
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) (K : WExtractedKey) (b : ℕ)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ) :
    wSeparatedCorrelationEnergy x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c K β ζ a =
      ∑ L ∈ wGramLabels (wCoprimeFiber x N S
          (wGramPrefix N a x η R S M Z K b j cap positive) c),
        wGramWeight K β ζ L *
          (wGramPairSum N a x η R S M Z K b j cap positive c L).re := by
  let U := wGramPrefix N a x η R S M Z K b j cap positive
  let V := wCoprimeFiber x N S U c
  have hU := wGramPrefix_subset N a x η R S M Z K b j cap positive
  have hV : V ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K :=
    fun _ ht => hU (mem_filter.mp ht).1
  have hQ : ∀ q ∈ Ioc 0 ⌊R * S⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  let F : (WExtractedTuple × ℤ) → (WExtractedTuple × ℤ) → ℂ := fun t u =>
    ((wCorrelationInnerWeight K β ζ t : ℂ) *
      star (wCorrelationInnerWeight K β ζ u : ℂ)) *
      (wExtractedArithmeticPhase a t.2 t.1 *
        star (wExtractedArithmeticPhase a u.2 u.1))
  have henergy : wSeparatedCorrelationEnergy x N S U c K β ζ a =
      (∑ p ∈ wGramPairs V, F p.1 p.2).re := by
    rw [← sum_wGramPairs V F]
    unfold wSeparatedCorrelationEnergy
    rw [Complex.re_sum]
    apply sum_congr rfl
    intro o _
    congr 1
    apply sum_congr rfl
    intro t ht
    apply sum_congr rfl
    intro u hu
    obtain ⟨ht, hto⟩ := mem_filter.mp ht
    obtain ⟨hu, huo⟩ := mem_filter.mp hu
    have ho := hto.trans huo.symm
    have hk := congrArg Prod.fst ho
    have hr := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) ho
    have hn := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) ho
    dsimp only [F]
    rw [wCoprimeFiber_arithmetic_correlation hN hQ hU ht hu hk hr hn]
    ring
  rw [henergy, sum_wGramLabels V F, Complex.re_sum]
  apply sum_congr rfl
  intro L hL
  obtain ⟨hf, hf', hΔ, hΔ', he⟩ := wGramLabels_eligible hN hQ hV hL
  have hsection := wKSectionSlice_weighted_pair_eq (a := a) (x := x) (η := η)
    (b := b) (h := L.2.1.2.2) (h' := L.2.2.2.2) hN hR hS hM hZ
    hf hf' hΔ hΔ' he j cap positive c β ζ
  change (∑ t ∈ wKSectionSlice V L.1.1 L.1.2 L.2.1.1 L.2.1.2.1 L.2.1.2.2,
      ∑ u ∈ wKSectionSlice V L.1.1 L.1.2 L.2.2.1 L.2.2.2.1 L.2.2.2.2,
        if (wGCDTuple (wExtractedOriginal t.1)).k₁ =
            (wGCDTuple (wExtractedOriginal u.1)).k₁ then F t u else 0).re = _
  dsimp only [F, V, U, wGramPrefix]
  rw [hsection]
  simp only [wGramWeight, wGramPairSum, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
