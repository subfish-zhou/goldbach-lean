

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIPrimitiveBilinear

/-!
 # Actual tensor energy and rectangle aggregation for Vaughan Type II

This module bounds the coefficient obtained after collecting `t=e*m` by
Cauchy on the *actual fibre*.  The subsequent sum remains a sum in `(d,t)`;
it is never repackaged pointwise in `n=d*e*m`.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The actual `e`-fibre above `t`, including the physical cutoff on `m`. -/
def vaughanTensorFiber (y d : ℕ) (ES : Finset ℕ) (t : ℤ) : Finset ℕ :=
  ES.filter fun e => ∃ m ∈ Finset.Icc 1 (y / (d * e)), ((e * m : ℕ) : ℤ) = t


private theorem tensor_inner_sum_eq_indicator
    (z : ℂ) (y d e : ℕ) (t : ℤ) (he : 0 < e) :
    (∑ m ∈ Finset.Icc 1 (y / (d * e)),
      if ((e * m : ℕ) : ℤ) = t then z else 0) =
      if ∃ m ∈ Finset.Icc 1 (y / (d * e)), ((e * m : ℕ) : ℤ) = t then z else 0 := by
  by_cases h : ∃ m ∈ Finset.Icc 1 (y / (d * e)), ((e * m : ℕ) : ℤ) = t
  · obtain ⟨m, hm, hmt⟩ := h
    rw [if_pos ⟨m, hm, hmt⟩]
    rw [Finset.sum_eq_single m]
    · simp [hmt]
    · intro m' hm' hne
      rw [if_neg]
      intro hm't
      apply hne
      apply Nat.eq_of_mul_eq_mul_left he
      exact_mod_cast hm't.trans hmt.symm
    · intro hmnot
      exact False.elim (hmnot hm)
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    exact fun hmt => h ⟨m, hm, hmt⟩

/-- Exact fibre form of the actual Vaughan tensor coefficient. -/
theorem vaughanBilinearTensorCoeff_eq_fiber
    (b : ℕ → ℂ) (y d : ℕ) (ES : Finset ℕ) (t : ℤ)
    (hES : ∀ e ∈ ES, 0 < e) :
    vaughanBilinearTensorCoeff vaughanMangoldtCoeff b y d ES t =
      ∑ e ∈ vaughanTensorFiber y d ES t,
        vaughanMangoldtCoeff e * b (d * t.toNat) := by
  unfold vaughanBilinearTensorCoeff vaughanTensorFiber
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  rw [tensor_inner_sum_eq_indicator
    (vaughanMangoldtCoeff e * b (d * t.toNat)) y d e t (hES e he)]


end

end AnalyticNumberTheory.LargeSieve
