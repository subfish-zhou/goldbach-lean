import MathlibNt.SieveTheory.LiLiuFouvryG9IntegerFibre
import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedSieve
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9LongCoefficient

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The full ordered divisor convolution, including the zero input. -/
theorem fouvryTau_two_one_convolution (v : ℕ) :
    (∑ p ∈ v.divisorsAntidiagonal,
      (fouvryTau 2 p.1 : ℝ) * (fouvryTau 1 p.2 : ℝ)) = (fouvryTau 3 v : ℝ) := by
  norm_cast
  rw [← ArithmeticFunction.mul_apply]
  congr 1
  simp only [fouvryTau, ← pow_add]

/-- Arbitrary rectangular weights retain their actual product multiplicities.
No positive-support assumption is needed: the divisor weights kill zero factors. -/
theorem fouvryG9_weighted_product_fibre_le
    (U V : Finset ℕ) (α β : ℕ → ℝ) (v : ℕ)
    (hα : ∀ m ∈ U, 0 ≤ α m ∧ α m ≤ (fouvryTau 2 m : ℝ))
    (hβ : ∀ n ∈ V, 0 ≤ β n ∧ β n ≤ (fouvryTau 1 n : ℝ)) :
    (∑ p ∈ U ×ˢ V, if p.1 * p.2 = v then α p.1 * β p.2 else 0) ≤
      (fouvryTau 3 v : ℝ) := by
  classical
  by_cases hv : v = 0
  · subst v
    have hz : ∀ p ∈ U ×ˢ V,
        (if p.1 * p.2 = 0 then α p.1 * β p.2 else 0) = 0 := by
      intro p hp
      obtain ⟨hm, hn⟩ := mem_product.mp hp
      split_ifs with h
      · rcases Nat.mul_eq_zero.mp h with h | h
        · have ha := hα p.1 hm
          have ha0 : α p.1 = 0 := le_antisymm (by simpa [h] using ha.2) ha.1
          simp [ha0]
        · have hb := hβ p.2 hn
          have hb0 : β p.2 = 0 := le_antisymm (by simpa [h] using hb.2) hb.1
          simp [hb0]
      · rfl
    rw [Finset.sum_congr rfl hz]
    simp
  · rw [← Finset.sum_filter]
    calc
      (∑ p ∈ (U ×ˢ V).filter (fun p => p.1 * p.2 = v), α p.1 * β p.2) ≤
          ∑ p ∈ (U ×ˢ V).filter (fun p => p.1 * p.2 = v),
            (fouvryTau 2 p.1 : ℝ) * (fouvryTau 1 p.2 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hm, hn⟩ := mem_product.mp (mem_filter.mp hp).1
        exact mul_le_mul (hα p.1 hm).2 (hβ p.2 hn).2 (hβ p.2 hn).1
          (Nat.cast_nonneg _)
      _ ≤ ∑ p ∈ v.divisorsAntidiagonal,
            (fouvryTau 2 p.1 : ℝ) * (fouvryTau 1 p.2 : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hp).2, hv⟩
        · intro p _ _
          positivity
      _ = _ := fouvryTau_two_one_convolution v

/-- The integer absolute-difference fibre has at most two natural product values.
Natural subtraction is retained, even when the radius exceeds the centre. -/
theorem fouvryG9_natAbs_product_values (N m n r : ℕ)
    (h : ((N : ℤ) - (m : ℤ) * n).natAbs = r) :
    m * n = N + r ∨ m * n = N - r := by
  rw [← Nat.cast_mul] at h
  rcases Int.natAbs_eq_iff.mp h with h | h
  · right
    omega
  · left
    omega

/-- A genuine weighted absolute-difference multiplicity bound, with no `r ≤ N`
premise. At radius zero the harmless doubled upper bound is intentional. -/
theorem fouvryG9_weighted_natAbs_fibre_le
    (U V : Finset ℕ) (α β : ℕ → ℝ) (N r : ℕ)
    (hα : ∀ m ∈ U, 0 ≤ α m ∧ α m ≤ (fouvryTau 2 m : ℝ))
    (hβ : ∀ n ∈ V, 0 ≤ β n ∧ β n ≤ (fouvryTau 1 n : ℝ)) :
    (∑ p ∈ U ×ˢ V,
      if ((N : ℤ) - (p.1 : ℤ) * p.2).natAbs = r then α p.1 * β p.2 else 0) ≤
      (fouvryTau 3 (N + r) : ℝ) + (fouvryTau 3 (N - r) : ℝ) := by
  classical
  calc
    _ ≤ ∑ p ∈ U ×ˢ V,
        ((if p.1 * p.2 = N + r then α p.1 * β p.2 else 0) +
         (if p.1 * p.2 = N - r then α p.1 * β p.2 else 0)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hm, hn⟩ := mem_product.mp hp
      have hw : 0 ≤ α p.1 * β p.2 := mul_nonneg (hα p.1 hm).1 (hβ p.2 hn).1
      by_cases h : ((N : ℤ) - (p.1 : ℤ) * p.2).natAbs = r
      · obtain hplus | hminus := fouvryG9_natAbs_product_values N p.1 p.2 r h
        · simp only [h, hplus, if_true]
          split_ifs <;> linarith
        · simp only [h, hminus, if_true]
          split_ifs <;> linarith
      · simp only [h, if_false]
        split_ifs <;> linarith
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (fouvryG9_weighted_product_fibre_le U V α β (N + r) hα hβ)
      (fouvryG9_weighted_product_fibre_le U V α β (N - r) hα hβ)

/-- Beyond the centre the lower product is zero and has zero divisor weight. -/
theorem fouvryG9_weighted_natAbs_fibre_le_of_lt
    (U V : Finset ℕ) (α β : ℕ → ℝ) (N r : ℕ) (hNr : N < r)
    (hα : ∀ m ∈ U, 0 ≤ α m ∧ α m ≤ (fouvryTau 2 m : ℝ))
    (hβ : ∀ n ∈ V, 0 ≤ β n ∧ β n ≤ (fouvryTau 1 n : ℝ)) :
    (∑ p ∈ U ×ˢ V,
      if ((N : ℤ) - (p.1 : ℤ) * p.2).natAbs = r then α p.1 * β p.2 else 0) ≤
      (fouvryTau 3 (N + r) : ℝ) := by
  simpa [Nat.sub_eq_zero_of_le hNr.le] using
    fouvryG9_weighted_natAbs_fibre_le U V α β N r hα hβ

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
