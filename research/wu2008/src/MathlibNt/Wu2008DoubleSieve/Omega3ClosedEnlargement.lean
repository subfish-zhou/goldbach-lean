import MathlibNt.Wu2008DoubleSieve.Omega3LabelsCofactor

/-!
# Explicit comparison with the source's closed upper prime endpoint

The strict switched sequence used in the proved bound is enlarged here.
No equality of strict and closed masses or endpoint error estimate is asserted.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def omega3CofactorPrimeFibreLE (N : ℕ) (δ s : ℝ)
    (c : Omega3CofactorIndex) : Finset ℕ :=
  (range (N + 1)).filter fun p =>
    p.Prime ∧ c.2.1 < p ∧ (p : ℝ) ≤ wuLocalCutoff N δ c.1 s ∧
      omega3CofactorValue c * p ≤ N

noncomputable def omega3SwitchedSiftedCountLE {i : ℕ} (N : ℕ) (δ s t Z : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ) *
    (((omega3CofactorPrimeFibreLE N δ s c).filter
      (fun p => Sifted N (N - omega3CofactorValue c * p) Z)).card : ℝ)

/-- For positive e this closed range is p2<p<=min(N/e,z). It also drops
the original p-coprime-to-N restriction, so is explicitly an enlargement. -/
theorem omega3_prime_fibre_subset_closed {N : ℕ} {δ s : ℝ} {c : Omega3CofactorIndex}
    (he : 0 < omega3CofactorValue c) :
    omega3CofactorPrimeFibre N δ s c ⊆ omega3CofactorPrimeFibreLE N δ s c := by
  intro p hp
  obtain ⟨hp, hlow, hsize⟩ := mem_filter.mp hp
  have hp' := mem_primeWindow.mp hp
  have hpN : p ≤ N := (Nat.le_mul_of_pos_left p he).trans hsize
  exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hpN),
    hp'.1, hlow, hp'.2.2.2.le, hsize⟩

theorem omega3_switched_sifted_le_closed {i : ℕ} (N : ℕ) (δ s t Z : ℝ)
    (W : Fin i → Finset ℕ) (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    omega3SwitchedSiftedCount N δ s t Z W ≤ omega3SwitchedSiftedCountLE N δ s t Z W := by
  rw [omega3_switched_sifted_cofactor_first]
  apply sum_le_sum
  intro c hc
  rcases c with ⟨d, p2, p1, n⟩
  obtain ⟨hd', h2, h1, _, hn, _, _⟩ := mem_omega3CofactorLabels.mp hc
  have he : 0 < omega3CofactorValue ⟨d, p2, p1, n⟩ :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hd d hd') hn) (mem_primeWindow.mp h1).1.pos)
      (mem_primeWindow.mp h2).1.pos
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact_mod_cast card_le_card (filter_subset_filter _ (omega3_prime_fibre_subset_closed he))

end Wu2008DoubleSieve
