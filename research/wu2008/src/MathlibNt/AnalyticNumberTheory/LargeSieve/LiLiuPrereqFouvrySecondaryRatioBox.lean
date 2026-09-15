import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryRatioCount
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryResonanceReindex
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramResonanceScaleBox

/-!
# The ratio-counting box for actual occupied secondary bases

The sign of both frequencies is fixed by the original block. Absolute values
therefore give an injection, without identifying positive and negative labels.
The three beta coordinates retain their distinct multiplicities.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def secondaryRatioQuadruples (H B : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Ioc 0 H ×ˢ Ico B (2 * B)) ×ˢ (Ioc 0 H ×ˢ Ioc 0 (2 * B))).filter
    (fun p => p.2.1 * p.1.2 = p.1.1 * p.2.2)

theorem secondaryRatioQuadruples_card (H B : ℕ) :
    (secondaryRatioQuadruples H B).card =
      ∑ h ∈ Ioc 0 H, ∑ s ∈ Ico B (2 * B),
        (secondaryRatioPartners H (2 * B) h s).card := by
  simp only [secondaryRatioQuadruples, secondaryRatioPartners, card_eq_sum_ones,
    sum_filter, sum_product]

theorem secondaryRatioQuadruples_card_le {B : ℕ} (hB : 0 < B) (H : ℕ) :
    ((secondaryRatioQuadruples H B).card : ℝ) ≤
      4 * H * B * (1 + Real.log H) := by
  rw [secondaryRatioQuadruples_card]
  push_cast
  exact secondaryRatioPartners_dyadic_sum_le hB H

theorem secondary_frequency_natAbs_injective (i : ℕ) (positive : Bool) :
    Set.InjOn Int.natAbs (wGramResonanceScaleFrequencies i positive) := by
  intro h hh k hk he
  obtain ⟨m, _, rfl⟩ := mem_image.mp hh
  obtain ⟨n, _, rfl⟩ := mem_image.mp hk
  cases positive <;> simpa using he

theorem wGramPrefix_coordinate_mem_scale
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c) (i : Fin 5) :
    wAnalyticCoordinates t i ∈ wGramResonanceScaleInterval (j i) := by
  have hb := (mem_filter.mp (mem_filter.mp ht).1).1
  have he := congrFun (mem_filter.mp hb).2.1 i
  have hp := wAnalyticCoordinates_pos hN (fun _ hq => (mem_Ioc.mp hq).1)
    (mem_filter.mp hb).1 i
  exact mem_Ico.mpr ((Nat.log_eq_iff (Or.inr ⟨by decide, hp.ne'⟩)).mp he)

theorem wGramPrefix_frequency_mem_scale
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c) :
    t.2 ∈ wGramResonanceScaleFrequencies (j 0) positive := by
  have hn : t.2.natAbs ∈ wGramResonanceScaleInterval (j 0) :=
    wGramPrefix_coordinate_mem_scale hN ht 0
  have hs := (mem_filter.mp (mem_filter.mp (mem_filter.mp ht).1).1).2.2
  apply mem_image.mpr
  refine ⟨t.2.natAbs, hn, ?_⟩
  cases positive
  · have hh : t.2 ≤ 0 := by simpa using hs
    simp only [Bool.false_eq_true, ↓reduceIte, Int.natCast_natAbs,
      abs_of_nonpos hh, neg_neg]
  · have hh : 0 < t.2 := by simpa using hs
    simp only [↓reduceIte, Int.natCast_natAbs, abs_of_pos hh]

/-- An occupied seven-coordinate base supplies every scale bound before
any extension to a Cartesian box is made. -/
theorem wGramSecondaryBases_scale_data
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {F : ℕ} (hNF : ∀ n ∈ N, n ≤ F)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {v : WGramSecondaryBase}
    (hv : v ∈ wGramSecondaryBases (wGramSecondaryLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c))) :
    v.1 ∈ wGramResonanceScaleInterval (j 2) ∧
    v.2.1.1 ∈ Ioc 0 (F / K.1.1) ∧ v.2.2.1 ∈ Ioc 0 (F / K.1.1) ∧
    v.2.1.2.1 ∈ wGramResonanceScaleInterval (j 4) ∧
    v.2.2.2.1 ∈ wGramResonanceScaleInterval (j 4) ∧
    v.2.1.2.2 ∈ wGramResonanceScaleFrequencies (j 0) positive ∧
    v.2.2.2.2 ∈ wGramResonanceScaleFrequencies (j 0) positive ∧
    v.2.2.2.2 * v.2.1.2.1 = v.2.1.2.2 * v.2.2.2.1 := by
  obtain ⟨L, hL, rfl⟩ := mem_image.mp hv
  obtain ⟨hL, _, hsec⟩ := mem_filter.mp hL
  have hV := wGramCoprimePrefix_subset N a x η R S M Z K b j cap positive c
  obtain ⟨hf, hf', _⟩ := wGramLabels_eligible hN (fun _ hq => (mem_Ioc.mp hq).1) hV hL
  obtain ⟨hsupp, hsupp', _⟩ := wGramLabels_fixedSupport hN hR hS hM hZ hV hL
  have hm₁ : L.2.1.1 ∈ Ioc 0 (F / K.1.1) := by
    refine mem_Ioc.mpr ⟨hf.2.2.2.2.2.2.2.2.1, ?_⟩
    apply (Nat.le_div_iff_mul_le hf.1).mpr
    simpa only [mul_comm] using hNF _ hsupp.2.2.2.1
  have hm₂ : L.2.2.1 ∈ Ioc 0 (F / K.1.1) :=
    (wGramLabels_second_beta_le_upper hN hNF hR hS hM hZ hV hL).2
  obtain ⟨⟨t, u⟩, hp, rfl⟩ := mem_image.mp hL
  obtain ⟨ht, hu⟩ := mem_product.mp (mem_filter.mp hp).1
  exact ⟨wGramPrefix_coordinate_mem_scale hN ht 2, hm₁, hm₂,
    wGramPrefix_coordinate_mem_scale hN ht 4, wGramPrefix_coordinate_mem_scale hN hu 4,
    wGramPrefix_frequency_mem_scale hN ht, wGramPrefix_frequency_mem_scale hN hu, hsec⟩

abbrev WGramSecondaryRatioCode := (ℕ × ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))

def wGramSecondaryRatioCode (v : WGramSecondaryBase) : WGramSecondaryRatioCode :=
  ((v.1, v.2.1.1, v.2.2.1),
    ((v.2.1.2.2.natAbs, v.2.1.2.1), (v.2.2.2.2.natAbs, v.2.2.2.1)))

def wGramSecondaryRatioBox (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ) :
    Finset WGramSecondaryRatioCode :=
  (wGramResonanceScaleInterval (j 2) ×ˢ (Ioc 0 (F / K.1.1) ×ˢ Ioc 0 (F / K.1.1))) ×ˢ
    secondaryRatioQuadruples (2 ^ (j 0 + 1)) (2 ^ j 4)

theorem wGramSecondaryRatioBox_card_le (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ) :
    ((wGramSecondaryRatioBox K F j).card : ℝ) ≤
      (2 ^ j 2 : ℕ) * (F / K.1.1 : ℕ) ^ 2 *
        (4 * (2 ^ (j 0 + 1) : ℕ) * (2 ^ j 4 : ℕ) *
          (1 + Real.log (2 ^ (j 0 + 1) : ℕ))) := by
  simp only [wGramSecondaryRatioBox, card_product, wGramResonanceScaleInterval_card,
    Nat.card_Ioc, Nat.sub_zero, Nat.cast_mul]
  have hq := secondaryRatioQuadruples_card_le (by positivity : 0 < 2 ^ j 4)
    (2 ^ (j 0 + 1))
  simpa only [sq, mul_assoc] using
    mul_le_mul_of_nonneg_left hq (by positivity :
      (0 : ℝ) ≤ (2 ^ j 2 : ℕ) * ((F / K.1.1 : ℕ) * (F / K.1.1 : ℕ)))

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
