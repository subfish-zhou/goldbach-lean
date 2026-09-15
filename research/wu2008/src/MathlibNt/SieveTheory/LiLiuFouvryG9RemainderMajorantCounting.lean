import MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorant

noncomputable section
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Counting multiples by their value, not by injectivity of the source labels.
The range starts at zero: zero values are retained. -/
theorem fouvryG9RemainderMajorant_divCount {ι : Type*} (S : Finset ι)
    (a : ι → ℕ) (w : ι → ℝ) (L d : ℕ) (hd : 0 < d) (J : ℝ)
    (ha : ∀ x ∈ S, a x ≤ L)
    (hf : ∀ r ≤ L, (∑ x ∈ S, if a x = r then w x else 0) ≤ J) :
    (∑ x ∈ S, if d ∣ a x then w x else 0) ≤ J*((L/d : ℕ)+1 : ℕ) := by
  classical
  have heq : ∀ x ∈ S, (if d ∣ a x then w x else 0) =
      ∑ j ∈ range (L/d+1), if a x = j*d then w x else 0 := by
    intro x hx
    by_cases hdiv : d ∣ a x
    · rw [if_pos hdiv]
      symm
      rw [sum_eq_single (a x/d)]
      · rw [Nat.div_mul_cancel hdiv, if_pos rfl]
      · intro j _ hj
        apply if_neg
        intro he
        apply hj
        rw [he, Nat.mul_div_cancel _ hd]
      · intro h
        exact False.elim (h (mem_range.mpr (Nat.lt_succ_of_le
          (Nat.div_le_div_right (ha x hx)))))
    · rw [if_neg hdiv]
      symm
      apply sum_eq_zero
      intro j _
      apply if_neg
      intro he
      exact hdiv (he ▸ dvd_mul_left d j)
  calc
    _ = ∑ x ∈ S, ∑ j ∈ range (L/d+1), if a x = j*d then w x else 0 :=
      sum_congr rfl heq
    _ = ∑ j ∈ range (L/d+1), ∑ x ∈ S, if a x = j*d then w x else 0 := sum_comm
    _ ≤ ∑ _j ∈ range (L/d+1), J := by
      apply sum_le_sum
      intro j hj
      apply hf
      exact (Nat.le_div_iff_mul_le hd).mp (Nat.le_of_lt_succ (mem_range.mp hj))
    _ = _ := by simp [mul_comm]

/-- The elementary real estimate used for every d ≤ N. -/
theorem fouvryG9RemainderMajorant_multipleCount {N d : ℕ} (hd : 0 < d)
    (hdN : d ≤ N) : (((4*N)/d : ℕ)+1 : ℕ) ≤ 5*(N : ℝ)/d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply (le_div_iff₀ hdR).mpr
  have hq : (((4*N)/d : ℕ) : ℝ)*(d : ℝ) ≤ 4*(N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (4*N) d
  have hdn : (d : ℝ) ≤ N := by exact_mod_cast hdN
  push_cast
  nlinarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
