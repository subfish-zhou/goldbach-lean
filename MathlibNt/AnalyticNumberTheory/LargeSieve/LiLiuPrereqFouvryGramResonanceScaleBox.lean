import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramResonanceEnergy

/-!
# The local finite box of occupied resonance bases

The box keeps all five independent coordinates `(r,n₁,h,n₂',s')`.
Its frequency interval has the actual fixed sign. Its second beta width is
`F/d`, obtained from the original upper beta support, not from the first beta
coordinate. No positivity is assumed for keys with empty occupied carriers.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wGramResonanceScaleInterval (i : ℕ) : Finset ℕ :=
  Ico (2 ^ i) (2 ^ (i + 1))

theorem wGramResonanceScaleInterval_card (i : ℕ) :
    (wGramResonanceScaleInterval i).card = 2 ^ i := by
  simp only [wGramResonanceScaleInterval, Nat.card_Ico, pow_succ]
  omega

def wGramResonanceScaleFrequencies (i : ℕ) (positive : Bool) : Finset ℤ :=
  (wGramResonanceScaleInterval i).image
    (fun n : ℕ => if positive then (n : ℤ) else -(n : ℤ))

theorem wGramResonanceScaleFrequencies_card_le (i : ℕ) (positive : Bool) :
    (wGramResonanceScaleFrequencies i positive).card ≤ 2 ^ i := by
  exact (card_image_le).trans_eq (wGramResonanceScaleInterval_card i)

def wGramResonanceScaleBox (K : WExtractedKey) (F : ℕ)
    (j : Fin 5 → ℕ) (positive : Bool) : Finset WGramResonanceBase :=
  (wGramResonanceScaleInterval (j 3) ×ˢ wGramResonanceScaleInterval (j 2)) ×ˢ
    (wGramResonanceScaleFrequencies (j 0) positive ×ˢ
      (Ioc 0 (F / K.1.1) ×ˢ wGramResonanceScaleInterval (j 4)))

def wGramResonanceScaleBoxCard (K : WExtractedKey) (F : ℕ)
    (j : Fin 5 → ℕ) : ℕ :=
  2 ^ j 3 * 2 ^ j 2 * 2 ^ j 0 * (F / K.1.1) * 2 ^ j 4

theorem wGramResonanceScaleBox_card_le (K : WExtractedKey) (F : ℕ)
    (j : Fin 5 → ℕ) (positive : Bool) :
    (wGramResonanceScaleBox K F j positive).card ≤
      wGramResonanceScaleBoxCard K F j := by
  simp only [wGramResonanceScaleBox, card_product,
    wGramResonanceScaleInterval_card, Nat.card_Ioc, Nat.sub_zero]
  have hf := wGramResonanceScaleFrequencies_card_le (j 0) positive
  dsimp only [wGramResonanceScaleBoxCard]
  calc
    _ ≤ 2 ^ j 3 * 2 ^ j 2 * (2 ^ j 0 * (F / K.1.1 * 2 ^ j 4)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hf)
    _ = _ := by ring

private theorem prefix_coordinate_mem
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

private theorem prefix_frequency_mem
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {x η R S M Z : ℝ} {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c) :
    t.2 ∈ wGramResonanceScaleFrequencies (j 0) positive := by
  have hn : t.2.natAbs ∈ wGramResonanceScaleInterval (j 0) :=
    prefix_coordinate_mem hN ht 0
  have hs := (mem_filter.mp (mem_filter.mp (mem_filter.mp ht).1).1).2.2
  apply mem_image.mpr
  refine ⟨t.2.natAbs, hn, ?_⟩
  cases positive
  · have hh : t.2 ≤ 0 := by simpa using hs
    simp only [Bool.false_eq_true, ↓reduceIte, Int.natCast_natAbs,
      abs_of_nonpos hh, neg_neg]
  · have hh : 0 < t.2 := by simpa using hs
    simp only [↓reduceIte, Int.natCast_natAbs, abs_of_pos hh]

/-- Membership recovers positive `d` and the original `d*n₂' ∈ N`
before dividing by `d`. An empty label set requires no positive key. -/
theorem wGramLabels_second_beta_le_upper
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {F : ℕ} (hNF : ∀ n ∈ N, n ≤ F)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) {K : WExtractedKey} {b : ℕ}
    {V : Finset (WExtractedTuple × ℤ)}
    (hV : V ⊆ wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊R * S⌋₊) a
      (c2FiveSmallMask x η) R S (highOmegaCutoff x) b K)
    {L : WGramLabel} (hL : L ∈ wGramLabels V) :
    0 < K.1.1 ∧ L.2.2.1 ∈ Ioc 0 (F / K.1.1) := by
  have hf := (wGramLabels_eligible hN (fun _ hq => (mem_Ioc.mp hq).1) hV hL).2.1
  have hs := (wGramLabels_fixedSupport hN hR hS hM hZ hV hL).2.1
  refine ⟨hf.1, mem_Ioc.mpr ⟨hf.2.2.2.2.2.2.2.2.1, ?_⟩⟩
  apply (Nat.le_div_iff_mul_le hf.1).mpr
  simpa only [mul_comm] using hNF _ hs.2.2.2.1

/-- The inclusion is an identity injection into the Cartesian box; neither
beta coordinate nor the signed frequency is identified with another. -/
theorem wGramResonanceBases_subset_scaleBox
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {F : ℕ} (hNF : ∀ n ∈ N, n ≤ F)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) (K : WExtractedKey) (b : ℕ)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) :
    wGramResonanceBases (wGramZeroLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c)) ⊆
        wGramResonanceScaleBox K F j positive := by
  intro v hv
  obtain ⟨L, hL, rfl⟩ := mem_image.mp hv
  have hlabel := (mem_filter.mp hL).1
  have hn := (wGramLabels_second_beta_le_upper hN hNF hR hS hM hZ
    (wGramCoprimePrefix_subset N a x η R S M Z K b j cap positive c) hlabel).2
  obtain ⟨⟨t, u⟩, hp, rfl⟩ := mem_image.mp hlabel
  obtain ⟨ht, hu⟩ := mem_product.mp (mem_filter.mp hp).1
  exact mem_product.mpr
    ⟨mem_product.mpr ⟨prefix_coordinate_mem hN ht 3, prefix_coordinate_mem hN ht 2⟩,
      mem_product.mpr ⟨prefix_frequency_mem hN ht,
        mem_product.mpr ⟨hn, prefix_coordinate_mem hN hu 4⟩⟩⟩

theorem wGramResonanceBases_card_le_scaleBox
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {F : ℕ} (hNF : ∀ n ∈ N, n ≤ F)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) (K : WExtractedKey) (b : ℕ)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ)) :
    (wGramResonanceBases (wGramZeroLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c))).card ≤
        wGramResonanceScaleBoxCard K F j :=
  (card_le_card (wGramResonanceBases_subset_scaleBox
    hN hNF hR hS hM hZ K b j cap positive c)).trans
      (wGramResonanceScaleBox_card_le K F j positive)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
