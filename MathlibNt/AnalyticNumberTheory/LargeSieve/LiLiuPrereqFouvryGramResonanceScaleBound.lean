import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramResonanceScaleBox

/-!
# Quantitatively eliminating the occupied-base sum

The two power envelopes use only local dyadic highs and the original beta
upper support divided by `d`. Monotonicity is valid for every nonnegative
exponent, including empty carriers and degenerate arbitrary keys.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wGramResonanceScaleProductMax (K : WExtractedKey) (F : ℕ)
    (j : Fin 5 → ℕ) : ℕ :=
  2 ^ (j 0 + 1) * (F / K.1.1) * 2 ^ (j 4 + 1)

def wGramResonanceScaleDivisorMax (K : WExtractedKey) (F : ℕ)
    (j : Fin 5 → ℕ) : ℕ :=
  K.1.2.1 * 2 ^ (j 2 + 1) + wGramResonanceScaleProductMax K F j

def wGramResonanceScaleEnvelope (K : WExtractedKey) (F : ℕ)
    (j : Fin 5 → ℕ) (ε : ℝ) : ℝ :=
  (wGramResonanceScaleProductMax K F j : ℝ) ^ (2 * ε) *
    (wGramResonanceScaleDivisorMax K F j : ℝ) ^ ε

theorem wGramResonanceScaleEnvelope_nonneg (K : WExtractedKey) (F : ℕ)
    (j : Fin 5 → ℕ) (ε : ℝ) :
    0 ≤ wGramResonanceScaleEnvelope K F j ε := by
  unfold wGramResonanceScaleEnvelope
  positivity

private theorem frequency_natAbs_le
    {i : ℕ} {positive : Bool} {h : ℤ}
    (hh : h ∈ wGramResonanceScaleFrequencies i positive) :
    h.natAbs ≤ 2 ^ (i + 1) := by
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
  have hn' := (mem_Ico.mp hn).2.le
  cases positive <;> simpa using hn'

/-- Both power bases are bounded before taking any real powers. -/
theorem wGramResonanceScaleBox_bounds
    {K : WExtractedKey} {F : ℕ} {j : Fin 5 → ℕ} {positive : Bool}
    {v : WGramResonanceBase} (hv : v ∈ wGramResonanceScaleBox K F j positive) :
    (wGramResonanceProduct v).natAbs ≤ wGramResonanceScaleProductMax K F j ∧
      K.1.2.1 * v.1.2 + (wGramResonanceProduct v).natAbs ≤
        wGramResonanceScaleDivisorMax K F j := by
  obtain ⟨hrn, hrest⟩ := mem_product.mp hv
  obtain ⟨hh, hns⟩ := mem_product.mp hrest
  obtain ⟨hn, hs⟩ := mem_product.mp hns
  have hn₁ := (mem_Ico.mp (mem_product.mp hrn).2).2.le
  have hA : (wGramResonanceProduct v).natAbs ≤
      wGramResonanceScaleProductMax K F j := by
    simp only [wGramResonanceProduct, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul
      (Nat.mul_le_mul (frequency_natAbs_le hh) (mem_Ioc.mp hn).2)
      (mem_Ico.mp hs).2.le
  exact ⟨hA, Nat.add_le_add (Nat.mul_le_mul_left _ hn₁) hA⟩

theorem wGramResonanceScale_le_envelope
    {K : WExtractedKey} {F : ℕ} {j : Fin 5 → ℕ} {positive : Bool}
    {v : WGramResonanceBase} (hv : v ∈ wGramResonanceScaleBox K F j positive)
    {ε : ℝ} (hε : 0 ≤ ε) :
    wGramResonanceScale K ε v ≤ wGramResonanceScaleEnvelope K F j ε := by
  have hb := wGramResonanceScaleBox_bounds hv
  exact mul_le_mul
    (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hb.1)
      (mul_nonneg (by norm_num) hε))
    (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hb.2) hε)
    (by positivity) (by positivity)

/-- A proved cardinal-times-envelope estimate, not a hypothesis on the sum. -/
theorem sum_wGramResonanceScale_le_box
    {K : WExtractedKey} {F : ℕ} {j : Fin 5 → ℕ} {positive : Bool}
    {G : Finset WGramResonanceBase} (hG : G ⊆ wGramResonanceScaleBox K F j positive)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ v ∈ G, wGramResonanceScale K ε v) ≤
      (wGramResonanceScaleBoxCard K F j : ℝ) *
        wGramResonanceScaleEnvelope K F j ε := by
  have hc := (card_le_card hG).trans (wGramResonanceScaleBox_card_le K F j positive)
  calc
    _ ≤ ∑ _v ∈ G, wGramResonanceScaleEnvelope K F j ε :=
      sum_le_sum (fun _ hv => wGramResonanceScale_le_envelope (hG hv) hε)
    _ = (G.card : ℝ) * wGramResonanceScaleEnvelope K F j ε := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hc)
      (wGramResonanceScaleEnvelope_nonneg K F j ε)

/-- The actual local prefix supplies every box condition, including the
independent `n₂' ≤ F/d`; no positivity of an unoccupied key is required. -/
theorem wGramResonanceBases_sum_le_scaleBox
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {F : ℕ} (hNF : ∀ n ∈ N, n ≤ F)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) (K : WExtractedKey) (b : ℕ)
    (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∑ v ∈ wGramResonanceBases (wGramZeroLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c)),
        wGramResonanceScale K ε v) ≤
      (wGramResonanceScaleBoxCard K F j : ℝ) *
        wGramResonanceScaleEnvelope K F j ε :=
  sum_wGramResonanceScale_le_box
    (wGramResonanceBases_subset_scaleBox hN hNF hR hS hM hZ K b j cap positive c) hε

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
