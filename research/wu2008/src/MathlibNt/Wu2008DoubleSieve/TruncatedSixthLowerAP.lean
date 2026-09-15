import MathlibNt.Wu2008DoubleSieve.TruncatedSixthLowerSieve

/-!
# Absolute AP payment before imposing the curved pair mask

The windows are arbitrary prime windows, not source boxes. The
convolution coefficient retains all pair labels. The mask is applied
only to a sum of absolute errors.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem truncatedSixthLower_two_window_sum (P Q : Finset ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ boxConvolutionSupport ![P, Q], (convolutionCoeff ![P, Q] d : ℝ) * f d) =
      ∑ t ∈ P ×ˢ Q, f (t.1 * t.2) := by
  rw [boxConvolution_sum_fibres]
  have he : Fintype.piFinset ![P, Q] = (P ×ˢ Q).image (fun t => ![t.1, t.2]) := by
    ext t
    constructor
    · intro ht
      have hm := Fintype.mem_piFinset.mp ht
      refine mem_image.mpr ⟨(t 0, t 1), mem_product.mpr ⟨hm 0, hm 1⟩, ?_⟩
      funext j
      fin_cases j <;> rfl
    · intro ht
      obtain ⟨t, hmem, rfl⟩ := mem_image.mp ht
      apply Fintype.mem_piFinset.mpr
      intro j
      fin_cases j
      · exact (mem_product.mp hmem).1
      · exact (mem_product.mp hmem).2
  rw [he, sum_image]
  · apply sum_congr rfl
    intro t _
    simp
  · intro t _ u _ heq
    exact Prod.ext (congrFun heq 0) (congrFun heq 1)

theorem truncatedSixthLower_masked_remainder_le {N Q : ℕ}
    (P R : Finset ℕ) (S : Finset (ℕ × ℕ)) (hS : S ⊆ P ×ˢ R)
    (D : ℕ → ℕ) (z : ℝ)
    (hD : ∀ t ∈ S, D (t.1 * t.2) ≤ Q / (t.1 * t.2) + 1) :
    (∑ t ∈ S, |ordinaryRosserRemainder false N (t.1 * t.2) (D (t.1 * t.2)) z|) ≤
      convolutionAPError N Q ![P, R] := by
  rw [convolutionAPError_eq_support_sum]
  change _ ≤ ∑ d ∈ boxConvolutionSupport ![P, R], _
  rw [truncatedSixthLower_two_window_sum]
  calc
    _ ≤ ∑ t ∈ S,
        ∑ q ∈ (Icc 1 (Q / (t.1 * t.2))).filter (fun q => q.Coprime ((t.1 * t.2) * N)),
          |primeAPError N ((t.1 * t.2) * q) N| :=
      sum_le_sum (fun t ht => ordinaryRosserRemainder_le_AP z (hD t ht))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hS
      (fun _ _ _ => sum_nonneg (fun _ _ => abs_nonneg _))

theorem truncatedSixthLower_masked_AP_uniform {α δ A : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      ∀ (P R : Finset ℕ), (∀ p ∈ P, p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ α ≤ p) →
      (∀ q ∈ R, q.Prime ∧ q.Coprime N ∧ (N : ℝ) ^ α ≤ q) →
      ∀ S : Finset (ℕ × ℕ), S ⊆ P ×ˢ R → ∀ z : ℝ,
      (∑ t ∈ S, |ordinaryRosserRemainder false N (t.1 * t.2)
        (⌊(N : ℝ) ^ (1 / 2 - δ) / (t.1 * t.2 : ℕ)⌋₊ + 1) z|) ≤
          C * (N : ℝ) / log N ^ A := by
  obtain ⟨C, hC, T, hBV⟩ := convolution_bombieri_vinogradov 2 hα hδ hA
  refine ⟨C, hC, T, ?_⟩
  intro N hN P R hP hR S hS z
  have hW : ∀ j p, p ∈ (![P, R] : Fin 2 → Finset ℕ) j →
      p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ α ≤ p := by
    intro j p hp
    fin_cases j
    · exact hP p hp
    · exact hR p hp
  have h := truncatedSixthLower_masked_remainder_le (N := N) P R S hS
    (fun d => ⌊(N : ℝ) ^ (1 / 2 - δ) / d⌋₊ + 1) z
    (Q := convolutionModulusCutoff N δ) (by
      intro t _
      rw [Nat.floor_div_natCast]
      rfl)
  exact h.trans (hBV N hN 2 le_rfl ![P, R] hW)

end Wu2008DoubleSieve
