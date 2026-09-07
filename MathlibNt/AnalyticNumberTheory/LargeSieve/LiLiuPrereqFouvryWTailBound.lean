import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMaskedW
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmoothErrorBounds

/-!
# A constructed frequency cutoff and uniform masked tail bound

Choosing `H(q,r)=ceil(lcm(q,r)*Z/M)` makes the dimensionless frequency
cutoff at least `Z` for every modulus pair. The remaining coefficient
envelope is evaluated by the proved global fixed-order divisor means.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wUniformCutoff (M Z : ℝ) (q r : ℕ) : ℕ :=
  ⌈(q.lcm r : ℝ) / M * Z⌉₊

theorem wUniformCutoff_scale {M : ℝ} (hM : 0 < M) (Z : ℝ)
    {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) :
    Z ≤ (M / (q.lcm r : ℝ)) * wUniformCutoff M Z q r := by
  have hl : (0 : ℝ) < q.lcm r :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hq hr))
  calc
    Z = (M / (q.lcm r : ℝ)) * ((q.lcm r : ℝ) / M * Z) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) (div_pos hM hl).le

theorem sum_wMaskedTuples_abs_coefficient_le
    (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop) :
    (∑ t ∈ wMaskedTuples N Q a P, |wTupleCoefficient β c t|) ≤
      (∑ q ∈ Q, |c q|) ^ 2 * (∑ n ∈ N, |β n|) ^ 2 := by
  calc
    _ ≤ ∑ t ∈ (Q ×ˢ Q) ×ˢ (N ×ˢ N), |wTupleCoefficient β c t| := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro t ht
        have hs := (mem_filter.mp (mem_filter.mp ht).1).1
        simp only [mem_product] at hs ⊢
        exact ⟨⟨(mem_filter.mp hs.1.1).1, (mem_filter.mp hs.1.2).1⟩, hs.2⟩
      · intro t _ _
        exact abs_nonneg _
    _ = _ := by
      simp only [wTupleCoefficient, abs_mul, sum_product, ← sum_mul, ← mul_sum]
      ring

/-- The whole absolute tail envelope has a uniform `Z^(-l)` bound,
independently of the chosen arithmetic mask. -/
theorem wMaskedTailEnvelope_uniformCutoff_le
    (l : ℕ) {M Z : ℝ} (hM : 0 < M) (hZ : 0 < Z)
    (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) (P : WOriginalTuple → Prop)
    (hQ : ∀ q ∈ Q, q ≠ 0) :
    wMaskedTailEnvelope l M (wUniformCutoff M Z) N Q β c a P ≤
      ((∑ q ∈ Q, |c q|) ^ 2 * (∑ n ∈ N, |β n|) ^ 2) / Z ^ l := by
  calc
    _ ≤ ∑ t ∈ wMaskedTuples N Q a P, |wTupleCoefficient β c t| / Z ^ l := by
      apply sum_le_sum
      intro t ht
      obtain ⟨hq, hr, _, _⟩ := wMaskedTuples_spec ht
      have hb := wUniformCutoff_scale hM Z (hQ _ hq) (hQ _ hr)
      apply div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hZ l)
      exact pow_le_pow_left₀ hZ.le (by linarith) l
    _ = (∑ t ∈ wMaskedTuples N Q a P, |wTupleCoefficient β c t|) / Z ^ l :=
      (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right
      (sum_wMaskedTuples_abs_coefficient_le N Q β c a P) (pow_pos hZ l).le

/-- Explicit evaluation of the coefficient envelope for signed fixed-order
weights. The tail constant depends only on `l` and the fixed bump. -/
theorem wMaskedTail_uniformCutoff_fouvryTau (l : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M Z : ℝ, 0 < M → 0 < Z →
      ∀ k j : ℕ, 1 ≤ k → 1 ≤ j → ∀ T L : ℝ, 1 ≤ T → 1 ≤ L →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) → ∀ a : ℤ,
      ∀ P : WOriginalTuple → Prop,
      |wMaskedTail M (wUniformCutoff M Z) N Q β c a P| ≤
        C * ((L * (1 + Real.log L) ^ (j - 1)) ^ 2 *
          (T * (1 + Real.log T) ^ (k - 1)) ^ 2) / Z ^ l := by
  obtain ⟨C, hC, hb⟩ := wMaskedTail_uniform l
  refine ⟨C, hC, fun M Z hM hZ k j hk hj T L hT hL N Q hN hQ β c hβ hc a P ↦ ?_⟩
  have hQ0 : ∀ q ∈ Q, q ≠ 0 := fun q hq ↦ (mem_Ioc.mp (hQ hq)).1.ne'
  calc
    _ ≤ C * wMaskedTailEnvelope l M (wUniformCutoff M Z) N Q β c a P :=
      hb M hM _ N Q β c a P hQ0
    _ ≤ C * (((∑ q ∈ Q, |c q|) ^ 2 * (∑ n ∈ N, |β n|) ^ 2) / Z ^ l) :=
      mul_le_mul_of_nonneg_left
        (wMaskedTailEnvelope_uniformCutoff_le l hM hZ N Q β c a P hQ0) hC.le
    _ ≤ C * (((L * (1 + Real.log L) ^ (j - 1)) ^ 2 *
        (T * (1 + Real.log T) ^ (k - 1)) ^ 2) / Z ^ l) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply div_le_div_of_nonneg_right _ (pow_pos hZ l).le
      exact mul_le_mul
        (pow_le_pow_left₀ (sum_nonneg (fun _ _ ↦ abs_nonneg _))
          (sum_abs_le_fouvryTau_mean hj hL Q hQ c hc) 2)
        (pow_le_pow_left₀ (sum_nonneg (fun _ _ ↦ abs_nonneg _))
          (sum_abs_le_fouvryTau_mean hk hT N hN β hβ) 2)
        (sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
