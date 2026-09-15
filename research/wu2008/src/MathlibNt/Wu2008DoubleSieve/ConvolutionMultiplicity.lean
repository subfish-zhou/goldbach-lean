import MathlibNt.Wu2008DoubleSieve.ClosedLowerWeightFactors
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Finset

/-!
# Literal prime-window convolution and its divisor mass

The coefficient counts ordered tuples, not distinct products. In particular,
overlapping windows and repeated primes retain their full multiplicity.
This is the elementary bounded-multiplicity input for Wu (2004), (3.13).
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

/-- The literal coefficient of the convolution of the window indicators. -/
noncomputable def convolutionCoeff {k : ℕ} (W : Fin k → Finset ℕ) (d : ℕ) : ℕ :=
  ((Fintype.piFinset W).filter (fun t => ∏ j, t j = d)).card

theorem convolutionCoeff_zero_depth (W : Fin 0 → Finset ℕ) (d : ℕ) :
    convolutionCoeff W d = if d = 1 then 1 else 0 := by
  by_cases hd : d = 1 <;> simp [convolutionCoeff, hd, eq_comm]

theorem convolutionCoeff_pos_iff {k d : ℕ} {W : Fin k → Finset ℕ} :
    0 < convolutionCoeff W d ↔ ∃ t : Fin k → ℕ, (∀ j, t j ∈ W j) ∧ ∏ j, t j = d := by
  simp [convolutionCoeff, card_pos, Finset.Nonempty, Fintype.mem_piFinset]

/-- The genuine finite Dirichlet-convolution recursion. The base coefficient
is the unit at `1`, and adjoining a window convolves with its indicator. -/
theorem convolutionCoeff_cons {k : ℕ} (P : Finset ℕ) (W : Fin k → Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (d : ℕ) :
    convolutionCoeff (Fin.cons P W) d =
      ∑ p ∈ P, if p ∣ d then convolutionCoeff W (d / p) else 0 := by
  have hset :
      Fintype.piFinset (Fin.cons P W) =
        (P ×ˢ Fintype.piFinset W).map (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).toEmbedding := by
    simpa using filter_piFinset_eq_map_consEquiv
      (α := fun _ : Fin (k + 1) => ℕ) (Fin.cons P W) (fun _ => True)
  have hsum :
      convolutionCoeff (Fin.cons P W) d =
        ∑ p ∈ P, ((Fintype.piFinset W).filter (fun t => p * (∏ j, t j) = d)).card := by
    simp only [convolutionCoeff, hset, card_eq_sum_ones, sum_filter, sum_map, sum_product,
      Equiv.toEmbedding_apply, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
  rw [hsum]
  apply sum_congr rfl
  intro p hp
  have heq (e : ℕ) : p * e = d ↔ p ∣ d ∧ e = d / p := by
    constructor
    · intro he
      refine ⟨he ▸ dvd_mul_right p e, ?_⟩
      rw [← he, Nat.mul_div_cancel_left e (hP p hp)]
    · rintro ⟨hd, rfl⟩
      exact Nat.mul_div_cancel' hd
  by_cases hpd : p ∣ d
  · simp only [heq, hpd, true_and, if_true, convolutionCoeff]
  · simp [heq, hpd]

theorem convolutionCoeff_coprime {k d N : ℕ} {W : Fin k → Finset ℕ}
    (hW : ∀ j p, p ∈ W j → p.Coprime N) (hd : 0 < convolutionCoeff W d) :
    d.Coprime N := by
  obtain ⟨t, ht, rfl⟩ := convolutionCoeff_pos_iff.mp hd
  exact Nat.Coprime.prod_left fun j _ => hW j (t j) (ht j)

/-- An exact partition into product fibres, including nonsquarefree products. -/
theorem convolutionCoeff_sum_divisors {k m : ℕ} (W : Fin k → Finset ℕ)
    (hm : m ≠ 0) :
    ∑ d ∈ m.divisors, convolutionCoeff W d =
      ((Fintype.piFinset W).filter (fun t => (∏ j, t j) ∣ m)).card := by
  simpa [convolutionCoeff, Nat.mem_divisors, hm] using
    sum_card_fiberwise_eq_card_filter (Fintype.piFinset W) m.divisors
      (fun t => ∏ j, t j)

/-- Uniform divisor mass for arbitrary finite prime windows above `N^α`.
No squarefreeness, disjointness, ordering, or upper-window bound is required. -/
theorem convolutionCoeff_divisor_mass_le {k N m : ℕ} {α : ℝ}
    (W : Fin k → Finset ℕ) (hN : 1 < N) (hm : 0 < m) (hmN : m ≤ N)
    (hα : 0 < α)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ) ^ α ≤ (p : ℝ)) :
    ((∑ d ∈ m.divisors, convolutionCoeff W d : ℕ) : ℝ) ≤ (1 / α) ^ k := by
  let P := largePrimeDivisors m ((N : ℝ) ^ α)
  have hsub :
      (Fintype.piFinset W).filter (fun t => (∏ j, t j) ∣ m) ⊆
        Fintype.piFinset (fun _ : Fin k => P) := by
    intro t ht
    obtain ⟨ht, htm⟩ := mem_filter.mp ht
    apply Fintype.mem_piFinset.mpr
    intro j
    obtain ⟨hp, hlow⟩ := hW j (t j) (Fintype.mem_piFinset.mp ht j)
    exact mem_largePrimeDivisors.mpr
      ⟨hp, (dvd_prod_of_mem t (mem_univ j)).trans htm, Nat.ne_of_gt hm, hlow⟩
  rw [convolutionCoeff_sum_divisors W (Nat.ne_of_gt hm)]
  calc
    _ ≤ ((Fintype.piFinset (fun _ : Fin k => P)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    _ = (P.card : ℝ) ^ k := by simp
    _ ≤ (1 / α) ^ k :=
      pow_le_pow_left₀ (Nat.cast_nonneg _)
        (largePrimeDivisors_card_le_inv hN hm hmN hα) k

theorem convolutionCoeff_divisor_mass_le_depth {i k N m : ℕ} {α : ℝ}
    (W : Fin i → Finset ℕ) (hik : i ≤ k)
    (hN : 1 < N) (hm : 0 < m) (hmN : m ≤ N) (hα : 0 < α)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ) ^ α ≤ (p : ℝ)) :
    ((∑ d ∈ m.divisors, convolutionCoeff W d : ℕ) : ℝ) ≤
      (max 1 (1 / α)) ^ k := by
  calc
    _ ≤ (1 / α) ^ i := convolutionCoeff_divisor_mass_le W hN hm hmN hα hW
    _ ≤ (max 1 (1 / α)) ^ i :=
      pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
    _ ≤ (max 1 (1 / α)) ^ k := pow_le_pow_right₀ (le_max_left _ _) hik

end Wu2008DoubleSieve
