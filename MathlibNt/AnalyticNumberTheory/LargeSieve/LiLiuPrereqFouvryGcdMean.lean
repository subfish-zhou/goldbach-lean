import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-!
# Fouvry's finite gcd mean

Fouvry (1987), Lemma 2, p. 622. The divisor expansion is finite and
uniform in the nonzero integer whose gcd is being averaged.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

theorem gcd_le_divisor_sum {a : ℕ} (ha : a ≠ 0) (n : ℕ) :
    a.gcd n ≤ ∑ d ∈ a.divisors, if d ∣ n then d else 0 := by
  have hg : a.gcd n ∈ a.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left a n, ha⟩
  calc
    a.gcd n = (if a.gcd n ∣ n then a.gcd n else 0) := by
      rw [if_pos (Nat.gcd_dvd_right a n)]
    _ ≤ ∑ d ∈ a.divisors, if d ∣ n then d else 0 :=
      Finset.single_le_sum (f := fun d => if d ∣ n then d else 0)
        (fun _ _ => Nat.zero_le _) hg

theorem sum_divisor_majorant (a N : ℕ) :
    (∑ n ∈ Ioc 0 N, ∑ d ∈ a.divisors, if d ∣ n then d else 0) =
      ∑ d ∈ a.divisors, d * (N / d) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  simp [Nat.Ioc_filter_dvd_card_eq_div, Nat.mul_comm]

theorem sum_gcd_le_divisor_floor {a : ℕ} (ha : a ≠ 0) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, a.gcd n) ≤ ∑ d ∈ a.divisors, d * (N / d) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ∑ d ∈ a.divisors, if d ∣ n then d else 0 :=
      Finset.sum_le_sum (fun n _ => gcd_le_divisor_sum ha n)
    _ = _ := sum_divisor_majorant a N

theorem sum_gcd_le {a : ℕ} (ha : a ≠ 0) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, a.gcd n) ≤ N * a.divisors.card := by
  calc
    _ ≤ ∑ d ∈ a.divisors, d * (N / d) := sum_gcd_le_divisor_floor ha N
    _ ≤ ∑ _d ∈ a.divisors, N :=
      Finset.sum_le_sum (fun d _ => Nat.mul_div_le N d)
    _ = _ := by simp [Nat.mul_comm]

theorem sum_int_gcd_le (a : ℤ) (ha : a ≠ 0) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, Int.gcd a n) ≤ N * a.natAbs.divisors.card := by
  simpa [Int.gcd] using
    sum_gcd_le (a := a.natAbs) (by simpa using ha) N

theorem sum_int_gcd_le_real (a : ℤ) (ha : a ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (Int.gcd a n : ℝ)) ≤
      x * (a.natAbs.divisors.card : ℝ) := by
  calc
    _ ≤ (⌊x⌋₊ : ℝ) * (a.natAbs.divisors.card : ℝ) := by
      exact_mod_cast sum_int_gcd_le a ha ⌊x⌋₊
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.floor_le hx) (by positivity)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
