import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryExtractedScale
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFloorCutoff

/-!
# Reusing the actual analytic reduction with a smaller frequency cutoff

The integral, signed coefficients, full modulus interval, and six-key box
are unchanged. Only the genuinely retained frequency set is made smaller.
-/

noncomputable section
open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wExtractedMaxFrequency_le_of_cutoff_le {M Z L : ℝ}
    (hM : 0 < M) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (H : ℕ → ℕ → ℕ)
    (hH : ∀ q ∈ Ioc 0 ⌊L⌋₊, ∀ r ∈ Ioc 0 ⌊L⌋₊,
      H q r ≤ wUniformCutoff M Z q r)
    (N : Finset ℕ) (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) :
    wExtractedMaxFrequency H N (Ioc 0 ⌊L⌋₊) a P R S ξ ≤
      ⌈L ^ 2 / M * Z⌉₊ := by
  unfold wExtractedMaxFrequency
  apply Finset.sup_le
  intro z hz
  obtain ⟨hq, hr⟩ := wExtractedOriginal_reducedModuli hz
  exact (hH _ (mem_filter.mp hq).1 _ (mem_filter.mp hr).1).trans
    (wUniformCutoff_le_fullLevel hM hZ hL
      (mem_filter.mp hq).1 (mem_filter.mp hr).1)

/-- A smaller cutoff uses the same explicit shell count and key loss.
This reuses the proved integral and grouping, without replacing a masked
sum by an unweighted interval. -/
theorem wMaskedFactorExtractedTruncated_key_bound_of_cutoff_le
    {M Z L : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (H : ℕ → ℕ → ℕ)
    (hH : ∀ q ∈ Ioc 0 ⌊L⌋₊, ∀ r ∈ Ioc 0 ⌊L⌋₊,
      H q r ≤ wUniformCutoff M Z q r)
    (N : Finset ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (x η R S ξ : ℝ) (hY : 1 ≤ x ^ η) :
    ∃ b ≤ Nat.log 2 ⌈L ^ 2 / M * Z⌉₊, ∃ y ∈ Set.Icc (1 / 2 : ℝ) 3,
      ∃ K ∈ wExtractedKeyBox (x ^ η),
        |wMaskedFactorExtractedTruncated M H N (Ioc 0 ⌊L⌋₊)
          β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ| ≤
          384 * M * (Nat.log 2 ⌈L ^ 2 / M * Z⌉₊ + 1 : ℕ) * (x ^ η) ^ 7 *
            ‖wExtractedKeyExponential H N (Ioc 0 ⌊L⌋₊)
              β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b K (M * y)‖ := by
  obtain ⟨b, hb, hw⟩ := wMaskedFactorExtractedTruncated_dyadic_bound
    M H N (Ioc 0 ⌊L⌋₊) β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ
  have hlog := Nat.log_mono_right (b := 2)
    (wExtractedMaxFrequency_le_of_cutoff_le hM hZ hL H hH N a
      (c2FiveSmallMask x η) R S ξ)
  obtain ⟨y, hy, _, hyb⟩ := wExtractedFrequencyBlock_le_max
    hM H N (Ioc 0 ⌊L⌋₊) β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b
  obtain ⟨K, hK, hKb⟩ := wExtractedBlockExponential_le_keyMax_power
    H N (Ioc 0 ⌊L⌋₊) β c₁ γ ζ a x η R S ξ b (M * y) hY
  refine ⟨b, hb.trans hlog, y, hy, K, hK, hw.trans ?_⟩
  calc
    _ ≤ (Nat.log 2 ⌈L ^ 2 / M * Z⌉₊ + 1 : ℕ) *
        (3 * M * ‖wExtractedBlockExponential H N (Ioc 0 ⌊L⌋₊)
          β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b (M * y)‖) := by
      apply mul_le_mul _ hyb (norm_nonneg _) (Nat.cast_nonneg _)
      exact_mod_cast Nat.add_le_add_right hlog 1
    _ ≤ (Nat.log 2 ⌈L ^ 2 / M * Z⌉₊ + 1 : ℕ) *
        (3 * M * (128 * (x ^ η) ^ 7 *
          ‖wExtractedKeyExponential H N (Ioc 0 ⌊L⌋₊)
            β c₁ γ ζ a (c2FiveSmallMask x η) R S ξ b K (M * y)‖)) := by
      gcongr
    _ = _ := by ring


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
