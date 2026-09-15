import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryModulusSupport
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMaskedW

/-!
# Same-mask zero mode for the two supported-modulus exclusions

An arbitrary further mask implying `δ₁ > Y` or `δ₂ > Y` is bounded after
taking absolute values. Beta and modulus coefficients remain signed; the
beta input is only its absolute mass. No Siegel--Walfisz hypothesis, mask
symmetry, or restriction of unmasked cancellation is used.
-/

noncomputable section

open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Any finite enclosure of the masked modulus pairs pays the same-mask
zero mode by its exact inverse-lcm mass times the squared absolute beta mass. -/
theorem wMaskedZeroMode_abs_le_modulus_pair_mass
    (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (F : Finset (ℕ × ℕ))
    (hP : ∀ t ∈ wOriginalTuples N Q a, P t → t.1 ∈ F) :
    |wMaskedZeroMode M N Q β c a P| ≤
      |M * dyadicCutoffMass| *
        (∑ p ∈ F, |c p.1 * c p.2 / (p.1.lcm p.2 : ℝ)|) *
        (∑ n ∈ N, |β n|) ^ 2 := by
  let G : WOriginalTuple → ℝ := fun t =>
    |M * dyadicCutoffMass| *
      |c t.1.1 * c t.1.2 / (t.1.1.lcm t.1.2 : ℝ)| * |β t.2.1 * β t.2.2|
  have hG (t : WOriginalTuple) : 0 ≤ G t := by dsimp [G]; positivity
  calc
    _ ≤ ∑ t ∈ wMaskedTuples N Q a P, G t := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro t _
      apply le_of_eq
      dsimp [G, wTupleCoefficient]
      simp only [abs_mul, abs_div, Nat.abs_cast]
      ring
    _ ≤ ∑ t ∈ F ×ˢ (N ×ˢ N), G t := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨ho, hp⟩ := mem_filter.mp ht
        exact mem_product.mpr ⟨hP t ho hp, (mem_product.mp (mem_filter.mp ho).1).2⟩
      · intro t _ _
        exact hG t
    _ = _ := by
      simp only [G, sum_product, abs_mul, ← mul_sum, ← sum_mul, pow_two]

/-- Uniform square-root saving for either canonical supported-modulus
exclusion and every further modulus/beta-dependent submask. Constants precede
all changing data; beta is arbitrary and the residue is any integer. -/
theorem wMaskedZeroMode_abs_le_modulus_support (j : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ L x Y : ℝ, 1 ≤ L → L ≤ x → 0 < Y →
      ∀ M : ℝ, ∀ N Q : Finset ℕ, Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, ∀ P : WOriginalTuple → Prop,
        (∀ t ∈ wOriginalTuples N Q a, P t →
          Y < ((wGCDTuple t).δ₁ : ℝ) ∨ Y < ((wGCDTuple t).δ₂ : ℝ)) →
      |wMaskedZeroMode M N Q β c a P| ≤
        C * |M * dyadicCutoffMass| * x ^ ε *
          (∑ n ∈ N, |β n|) ^ 2 * (1 + Real.log L) ^ 2 / Real.sqrt Y := by
  obtain ⟨C, hC, hbound⟩ := sum_abs_lcm_weight_sparse_pairs_uniform j hε
  refine ⟨C, hC, ?_⟩
  intro L x Y hL hLx hY M N Q hQ β c hc a P hP
  let F := (Q ×ˢ Q).filter (fun p =>
    p.1 ∈ largeSquareDivisorSet ⌊L⌋₊ (Real.sqrt Y) ∨
      p.2 ∈ largeSquareDivisorSet ⌊L⌋₊ (Real.sqrt Y))
  have hPF : ∀ t ∈ wOriginalTuples N Q a, P t → t.1 ∈ F := by
    intro t ht hp
    obtain ⟨hqr, _⟩ := mem_product.mp (mem_filter.mp ht).1
    obtain ⟨hq, hr⟩ := mem_product.mp hqr
    have hqQ : t.1.1 ∈ Q := (mem_filter.mp hq).1
    have hrQ : t.1.2 ∈ Q := (mem_filter.mp hr).1
    refine mem_filter.mpr ⟨mem_product.mpr ⟨hqQ, hrQ⟩, ?_⟩
    rcases hP t ht hp with hδ | hδ
    · exact Or.inl (deltaOne_mem_largeSquareDivisorSet _ _ _ (hQ hqQ) hY.le hδ)
    · exact Or.inr (deltaTwo_mem_largeSquareDivisorSet _ _ _ (hQ hrQ) hY.le hδ)
  have hF :
      (∑ p ∈ F, |c p.1 * c p.2 / (p.1.lcm p.2 : ℝ)|) ≤
        C * x ^ ε * (1 + Real.log L) ^ 2 / Real.sqrt Y :=
    hbound L x (Real.sqrt Y) hL hLx (Real.sqrt_pos.mpr hY) Q hQ c hc F
      (filter_subset _ _) (fun _ hp => (mem_filter.mp hp).2)
  calc
    _ ≤ |M * dyadicCutoffMass| *
        (∑ p ∈ F, |c p.1 * c p.2 / (p.1.lcm p.2 : ℝ)|) *
        (∑ n ∈ N, |β n|) ^ 2 :=
      wMaskedZeroMode_abs_le_modulus_pair_mass M N Q β c a P F hPF
    _ ≤ |M * dyadicCutoffMass| *
        (C * x ^ ε * (1 + Real.log L) ^ 2 / Real.sqrt Y) *
        (∑ n ∈ N, |β n|) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hF (abs_nonneg _)) (sq_nonneg _)
    _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
