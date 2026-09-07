import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMainJointAggregate
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryScaleEnergy

/-! # The joint main mean on the original occupied labels

The two differences are deduced from canonicality and the original beta
support before any extension of the r fiber. Both ordered beta indices
and both signed frequencies remain independent coordinates.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wGramMainJointCarrier_frequency_data (i : ℕ) (positive : Bool) :
    ∀ h ∈ wGramResonanceScaleFrequencies i positive,
      h ≠ 0 ∧ h.natAbs ≤ 2 ^ (i + 1) := by
  intro h hh
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ i).trans_le (mem_Ico.mp hn).1
  have hnhi := (mem_Ico.mp hn).2.le
  cases positive <;> simpa using And.intro hnpos.ne' hnhi

theorem wGramMainJointCarrier_scale_data
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {F : ℕ} (hNF : ∀ n ∈ N, n ≤ F)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {L : WGramLabel}
    (hL : L ∈ wGramLabels (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c)) :
    L.1.2 ∈ wGramResonanceScaleInterval (j 2) ∧
    L.2.1.1 ∈ Ioc 0 (F / K.1.1) ∧ L.2.2.1 ∈ Ioc 0 (F / K.1.1) ∧
    L.2.1.2.1 ∈ wGramResonanceScaleInterval (j 4) ∧
    L.2.2.2.1 ∈ wGramResonanceScaleInterval (j 4) ∧
    L.2.1.2.2 ∈ wGramResonanceScaleFrequencies (j 0) positive ∧
    L.2.2.2.2 ∈ wGramResonanceScaleFrequencies (j 0) positive := by
  have hV := wGramCoprimePrefix_subset N a x η R S M Z K b j cap positive c
  obtain ⟨hf, _, _⟩ := wGramLabels_eligible hN (fun _ hq => (mem_Ioc.mp hq).1) hV hL
  obtain ⟨hsupp, _, _⟩ := wGramLabels_fixedSupport hN hR hS hM hZ hV hL
  have hm₁ : L.2.1.1 ∈ Ioc 0 (F / K.1.1) := by
    refine mem_Ioc.mpr ⟨hf.2.2.2.2.2.2.2.2.1, ?_⟩
    apply (Nat.le_div_iff_mul_le hf.1).mpr
    simpa only [mul_comm] using hNF _ hsupp.2.2.2.1
  have hm₂ := (wGramLabels_second_beta_le_upper hN hNF hR hS hM hZ hV hL).2
  obtain ⟨⟨t, u⟩, hp, rfl⟩ := mem_image.mp hL
  obtain ⟨ht, hu⟩ := mem_product.mp (mem_filter.mp hp).1
  exact ⟨wGramPrefix_coordinate_mem_scale hN ht 2, hm₁, hm₂,
    wGramPrefix_coordinate_mem_scale hN ht 4, wGramPrefix_coordinate_mem_scale hN hu 4,
    wGramPrefix_frequency_mem_scale hN ht, wGramPrefix_frequency_mem_scale hN hu⟩

theorem wGramMainJointCarrier_data
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {F : ℕ} (hNF : ∀ n ∈ N, n ≤ F)
    {a : ℤ} {x η R S M Z T : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z)
    (hNT : ∀ n ∈ N, T ≤ (n : ℝ)) (hgap : x ^ η < T)
    {K : WExtractedKey} {b : ℕ} {j cap : Fin 5 → ℕ}
    {positive : Bool} {c : Finset (ℕ × ℕ)} {L : WGramLabel}
    (hL : L ∈ wGramMainLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c)) :
    mainRestrictedData K.1.2.1 a (2 ^ (j 2 + 1)) (F / K.1.1) (2 ^ (j 4 + 1))
      (wGramResonanceScaleFrequencies (j 0) positive) (wGramSecondaryBase L) := by
  obtain ⟨hL, hl, hmain⟩ := mem_filter.mp hL
  obtain ⟨hn, hm, hm', hs, hs', hh, hh'⟩ :=
    wGramMainJointCarrier_scale_data hN hNF hR hS hM hZ hL
  have hV := wGramCoprimePrefix_subset N a x η R S M Z K b j cap positive c
  obtain ⟨hf, hf', _⟩ := wGramLabels_eligible hN (fun _ hq => (mem_Ioc.mp hq).1) hV hL
  obtain ⟨hsup, hsup', _⟩ := wGramLabels_fixedSupport hN hR hS hM hZ hV hL
  have hinterval {i n : ℕ} (hn : n ∈ wGramResonanceScaleInterval i) :
      n ∈ Ioc 0 (2 ^ (i + 1)) :=
    mem_Ioc.mpr ⟨(by positivity : 0 < 2 ^ i).trans_le (mem_Ico.mp hn).1,
      (mem_Ico.mp hn).2.le⟩
  exact ⟨hinterval hn, hm, hm', hinterval hs, hinterval hs', hh, hh',
    wKSectionFixedSupport_resonance_difference_ne_zero hNT hgap hf hsup,
    wKSectionFixedSupport_resonance_difference_ne_zero hNT hgap hf' hsup', hmain, hl⟩

def wGramMainJointMean (δ Cτ Cjoint : ℝ) (a : ℤ) (K : WExtractedKey)
    (F : ℕ) (j : Fin 5 → ℕ) : ℝ :=
  let N := 2 ^ (j 2 + 1)
  let M := F / K.1.1
  let S := 2 ^ (j 4 + 1)
  let L := mainRestrictedMax a K.1.2.1 N M (2 ^ (j 0 + 1)) S
  (2 ^ (j 3 + 1) - 1 : ℕ) *
    (Real.sqrt ((N : ℝ) * M ^ 2 * S ^ 2 * (2 ^ j 0 : ℕ) ^ 2 * (Cτ * (L : ℝ) ^ δ)) *
      Real.sqrt (((N : ℝ) * M ^ 2 * (2 ^ j 0 : ℕ) ^ 2) *
        (Cjoint * S ^ 2 * (1 + Real.log S) * (L : ℝ) ^ δ)))

theorem wGramMainJointMean_nonneg (δ Cτ Cjoint : ℝ) (a : ℤ) (K : WExtractedKey)
    (F : ℕ) (j : Fin 5 → ℕ) :
    0 ≤ wGramMainJointMean δ Cτ Cjoint a K F j := by
  unfold wGramMainJointMean
  positivity

set_option maxHeartbeats 800000 in
/-- This estimate starts again at the occupied labels, not at the previously
expanded `iv3MainResidual`. Only nonnegative r summands are extended. -/
theorem wGramMainJointCarrier_sqrt_sum {δ : ℝ} (hδ : 0 < δ) :
    ∃ Cτ Cjoint : ℝ, 0 < Cτ ∧ 0 < Cjoint ∧
    ∀ (N : Finset ℕ) (F : ℕ) (a : ℤ) (x η R S M Z T : ℝ)
      (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
      (c : Finset (ℕ × ℕ)),
      a ≠ 0 → (∀ n ∈ N, 0 < n) → (∀ n ∈ N, n ≤ F) →
      0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      (∀ n ∈ N, T ≤ (n : ℝ)) → x ^ η < T →
      (∑ L ∈ wGramMainLabels K a (wCoprimeFiber x N S
        (wGramPrefix N a x η R S M Z K b j cap positive) c),
        Real.sqrt ((wGramModulus L).gcd (wGramNumerator K a L).natAbs : ℝ)) ≤
          wGramMainJointMean δ Cτ Cjoint a K F j := by
  obtain ⟨Cτ, Cjoint, hCτ, hCjoint, hmean⟩ := mainRestricted_sqrt_gcd_sum hδ
  refine ⟨Cτ, Cjoint, hCτ, hCjoint, ?_⟩
  intro N F a x η R S M Z T K b j cap positive c ha hN hNF hR hS hM hZ hNT hgap
  let G := wGramMainLabels K a (wCoprimeFiber x N S
    (wGramPrefix N a x η R S M Z K b j cap positive) c)
  let H := wGramResonanceScaleFrequencies (j 0) positive
  have hdata (v : WGramSecondaryBase) (hv : v ∈ wGramSecondaryBases G) :
      mainRestrictedData K.1.2.1 a (2 ^ (j 2 + 1)) (F / K.1.1) (2 ^ (j 4 + 1)) H v := by
    obtain ⟨L, hL, rfl⟩ := mem_image.mp hv
    exact wGramMainJointCarrier_data hN hNF hR hS hM hZ hNT hgap hL
  have hrsub (v : WGramSecondaryBase) :
      wGramSecondaryFiber G v ⊆ Ioc 0 (2 ^ (j 3 + 1) - 1) := by
    intro r hr
    have hr' := mem_Ioc.mp (wGramLabels_r_mem_dyadic hN
      (mem_filter.mp (mem_wGramSecondaryFiber.mp hr)).1)
    exact mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) hr'.1, hr'.2⟩
  have hb := hmean K.1.2.1 (2 ^ (j 2 + 1)) (F / K.1.1) (2 ^ (j 0 + 1))
    (2 ^ (j 4 + 1)) (2 ^ (j 3 + 1) - 1) a H (wGramSecondaryBases G)
    ha (by positivity) (wGramMainJointCarrier_frequency_data (j 0) positive) hdata
  have hc : (H.card : ℝ) ≤ (2 ^ j 0 : ℕ) := by
    exact_mod_cast wGramResonanceScaleFrequencies_card_le (j 0) positive
  have hlog : 0 ≤ 1 + Real.log (2 ^ (j 4 + 1) : ℕ) := by
    have := Real.log_nonneg
      (by exact_mod_cast (show 1 ≤ (2 : ℕ) ^ (j 4 + 1) by
          have : 0 < (2 : ℕ) ^ (j 4 + 1) := by positivity
          omega) :
        (1 : ℝ) ≤ (2 ^ (j 4 + 1) : ℕ))
    linarith
  calc
    _ = ∑ v ∈ wGramSecondaryBases G, ∑ r ∈ wGramSecondaryFiber G v,
        Real.sqrt ((wGramModulus (wGramSecondaryJoin v r)).gcd
          (wGramNumerator K a (wGramSecondaryJoin v r)).natAbs : ℝ) :=
      sum_wGramSecondaryFiber G (fun L =>
        Real.sqrt ((wGramModulus L).gcd (wGramNumerator K a L).natAbs : ℝ))
    _ ≤ ∑ v ∈ wGramSecondaryBases G, ∑ r ∈ Ioc 0 (2 ^ (j 3 + 1) - 1),
        Real.sqrt ((wGramModulus (wGramSecondaryJoin v r)).gcd
          (wGramNumerator K a (wGramSecondaryJoin v r)).natAbs : ℝ) :=
      sum_le_sum (fun v _ => sum_le_sum_of_subset_of_nonneg (hrsub v)
        (fun _ _ _ => Real.sqrt_nonneg _))
    _ ≤ _ := by
      apply hb.trans
      dsimp only [wGramMainJointMean]
      have hc2 : (H.card : ℝ) ^ 2 ≤ ((2 ^ j 0 : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg H.card) hc 2
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      · apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc2 (by positivity)) (by positivity)
      · apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc2 (by positivity)) (by positivity)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
