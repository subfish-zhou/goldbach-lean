

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanPrefixReduction

/-!
 # Genuine bilinear blocks for Vaughan Type II

This module performs the finite rearrangement before any pointwise square is
taken.  A dyadic rectangle in the large variables `d,e` is rewritten from a
prefix in `n` into the exact variables `n = d*e*m`; multiplicativity then puts
one character on each variable.  The final estimates apply Cauchy only in the
outer `d` variable and leave the complete `e,m` sum visible.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section


/-- Exact finite enumeration of the positive multiples of `k` in `[1,y]`.
This is the atomic `n = k*m` reindexing used with `k=d*e`. -/
theorem sum_multiples_Icc_reindex {R : Type*} [AddCommMonoid R]
    (F : ℕ → R) {k y : ℕ} (hk : 0 < k) :
    (∑ n ∈ (Finset.Icc 1 y).filter (fun n => k ∣ n), F n) =
      ∑ m ∈ Finset.Icc 1 (y / k), F (k * m) := by
  refine Finset.sum_bij (fun n _ => n / k) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter] at hn
    have hnI := Finset.mem_Icc.mp hn.1
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd hnI.1 hn.2) hk
    · exact Nat.div_le_div_right hnI.2
  · intro n₁ hn₁ n₂ hn₂ h
    rw [Finset.mem_filter] at hn₁ hn₂
    calc
      n₁ = k * (n₁ / k) := (Nat.mul_div_cancel' hn₁.2).symm
      _ = k * (n₂ / k) := by rw [h]
      _ = n₂ := Nat.mul_div_cancel' hn₂.2
  · intro m hm
    rw [Finset.mem_Icc] at hm
    refine ⟨k * m, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · constructor
        · exact Nat.mul_pos hk hm.1
        · simpa [mul_comm] using (Nat.le_div_iff_mul_le hk).mp hm.2
      · exact dvd_mul_right k m
    · exact Nat.mul_div_cancel_left m hk
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]


/-- Vaughan's actual factor weights for the Type-II rectangle. -/
def vaughanMoebiusCoeff (d : ℕ) : ℂ := ((ArithmeticFunction.moebius d : ℤ) : ℂ)

def vaughanMangoldtCoeff (e : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt e : ℂ)


end

end AnalyticNumberTheory.LargeSieve
