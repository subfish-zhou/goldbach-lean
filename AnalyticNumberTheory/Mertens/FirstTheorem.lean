module

public import Mathlib.Analysis.SpecialFunctions.Log.Sum
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Chebyshev

/-!
# Mertens' first theorem

The divisor identity for `log` reduces the von Mangoldt sum to the elementary
Chebyshev upper bound. Bounding the contribution of higher prime powers then
gives a bounded error in the prime sum.

The proof follows the Mertens development in `PrimeNumberTheoremAnd.IEANTN.Mertens`
(commit `938912bbff637bdb18025f0cfd62db3939b63b0a`), using the pinned Mathlib's
logarithmic sum bounds and Chebyshev estimates.
-/

@[expose] public section

namespace AnalyticNumberTheory.Mertens

open ArithmeticFunction (vonMangoldt_mul_zeta vonMangoldt_apply vonMangoldt_apply_prime
  vonMangoldt_nonneg sum_Ioc_mul_zeta_eq_sum)
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.zeta Chebyshev

private theorem sum_log_eq_sum_vonMangoldt (x : ℝ) :
    ∑ d ∈ Ioc 0 ⌊x⌋₊, log d = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have hlog (n : ℕ) : log n = (ArithmeticFunction.vonMangoldt * ArithmeticFunction.zeta) n := by
    rw [vonMangoldt_mul_zeta]
    rfl
  simp_rw [hlog, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

private theorem vonMangoldt_div_sum_bounds {x : ℝ} (hx : 1 ≤ x) :
    log x - 2 ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ∧
      ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ log x + (log 4 + 4) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hmul : x * (∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d) =
      ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [mul_sum]
    exact sum_congr rfl fun d _ => by ring
  constructor
  · apply le_of_mul_le_mul_left _ hx0
    rw [hmul]
    calc
      x * (log x - 2) = x * log x - 2 * x := by ring
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, log d := le_sum_log' hx
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
        rw [sum_log_eq_sum_vonMangoldt]
        exact sum_le_sum fun d _ => mul_le_mul_of_nonneg_left
          (Nat.floor_le (div_nonneg hx0.le (Nat.cast_nonneg d))) vonMangoldt_nonneg
  · apply le_of_mul_le_mul_left _ hx0
    rw [hmul]
    calc
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (↑⌊x / d⌋₊ + 1) :=
        sum_le_sum fun d _ => mul_le_mul_of_nonneg_left
          (Nat.lt_floor_add_one _).le vonMangoldt_nonneg
      _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ψ x := by
        simp_rw [mul_add, mul_one, sum_add_distrib, sum_log_eq_sum_vonMangoldt, Chebyshev.psi]
      _ ≤ x * log x + (log 4 + 4) * x :=
        add_le_add (sum_log_le' hx) (Chebyshev.psi_le_const_mul_self hx0.le)
      _ = x * (log x + (log 4 + 4)) := by ring

private noncomputable def primePowerBoundTerm (n : ℕ) : ℝ :=
  if n.Prime then log n / (n * ((n : ℝ) - 1)) else 0

private theorem primePowerBoundTerm_nonneg (n : ℕ) : 0 ≤ primePowerBoundTerm n := by
  unfold primePowerBoundTerm
  split_ifs with hn
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
    have hn1 : 0 ≤ (n : ℝ) - 1 := by linarith
    exact div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hn1)
  · exact le_rfl

private theorem summable_primePowerBoundTerm : Summable primePowerBoundTerm := by
  refine ((Real.summable_one_div_nat_rpow.mpr (by norm_num : 1 < (3 : ℝ) / 2)).const_div
    4).of_nonneg_of_le primePowerBoundTerm_nonneg fun n => ?_
  unfold primePowerBoundTerm
  split_ifs with hn
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
    have hden : (n : ℝ) ^ 2 / 2 ≤ n * ((n : ℝ) - 1) := by
      nlinarith [mul_nonneg hn0.le (show (0 : ℝ) ≤ n - 2 by linarith)]
    calc
      log n / (n * ((n : ℝ) - 1)) ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) /
          ((n : ℝ) ^ 2 / 2) :=
        div_le_div₀ (by positivity) (Real.log_le_rpow_div hn0.le (by norm_num))
          (by positivity) hden
      _ = 4 / (n : ℝ) ^ (3 / 2 : ℝ) := by
        have hpow : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) ^ 2 := by
          rw [← Real.rpow_add hn0, show (1 / 2 : ℝ) + 3 / 2 = 2 by norm_num, Real.rpow_two]
        field_simp
        linear_combination 4 * hpow
  · positivity

private theorem prime_div_sum_le_vonMangoldt_sum (x : ℝ) :
    (∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, log p / p) ≤
      ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d := by
  rw [sum_filter]
  apply sum_le_sum
  intro p _
  split_ifs with hp
  · rw [vonMangoldt_apply_prime hp]
  · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)

private theorem vonMangoldt_sum_le_prime_div_sum {x : ℝ} (hx : 1 ≤ x) :
    (∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d) ≤
      (∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, log p / p) + ∑' n, primePowerBoundTerm n := by
  let K := max 1 ⌊log x / log 2⌋₊
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter,
    Chebyshev.sum_PrimePow_eq_sum_sum _ (zero_le_one.trans hx)]
  calc
    _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊,
        ∑ p ∈ (Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime,
          log p / (p ^ k : ℕ) := by
      refine sum_congr rfl fun k hk => sum_congr rfl fun p hp => ?_
      rw [Nat.Prime.pow_minFac (mem_filter.mp hp).2 (by
        have := (mem_Icc.mp hk).1
        omega)]
    _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊,
        ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, log p / (p ^ k : ℕ) := by
      gcongr with k hk
      apply rpow_le_self_of_one_le hx
      exact (div_le_one₀ (by exact_mod_cast Nat.zero_lt_one.trans_le (mem_Icc.mp hk).1)).2
        (by exact_mod_cast (mem_Icc.mp hk).1)
    _ ≤ ∑ k ∈ Icc 1 K, ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, log p / (p ^ k : ℕ) :=
      sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (le_max_right _ _))
        (fun _ _ _ => sum_nonneg fun _ _ => by positivity)
    _ = (∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, log p / p) +
        ∑ k ∈ Ioc 1 K, ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, log p / (p ^ k : ℕ) := by
      rw [← add_sum_Ioc_eq_sum_Icc (le_max_left _ _)]
      simp [K]
    _ ≤ _ := by
      apply add_le_add_right
      rw [sum_comm]
      calc
        _ ≤ ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, primePowerBoundTerm p := by
          apply sum_le_sum
          intro p hp
          have hp' := (mem_filter.mp hp).2
          have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp'.one_lt
          simp only [primePowerBoundTerm, hp', ite_true, Nat.cast_pow, div_eq_mul_inv,
            ← mul_sum]
          apply mul_le_mul_of_nonneg_left _ (log_natCast_nonneg _)
          change ∑ k ∈ Ico 2 (K + 1), ((p : ℝ) ^ k)⁻¹ ≤ _
          simp_rw [← inv_pow]
          refine (geom_sum_Ico_le_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)).trans_eq ?_
          have hp0 : (p : ℝ) ≠ 0 := by positivity
          have hsub : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
          field_simp
        _ ≤ _ := summable_primePowerBoundTerm.sum_le_tsum _ (fun n _ =>
          primePowerBoundTerm_nonneg n)

/-- Mertens' first theorem, with a uniform bounded remainder for all `x ≥ 1`. -/
theorem mertensFirst :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x → |(∑ p ∈ ⌊x⌋₊.primesLE, log p / p) - log x| ≤ C := by
  let B := ∑' n, primePowerBoundTerm n
  have hB : 0 ≤ B := tsum_nonneg primePowerBoundTerm_nonneg
  have hlog : 0 ≤ log 4 := log_nonneg (by norm_num)
  refine ⟨log 4 + 4 + B, by linarith, ?_⟩
  intro x hx
  rw [Nat.primesLE_eq_filter_Icc_one]
  change |(∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, log p / p) - log x| ≤ _
  have ⟨hlo, hhi⟩ := vonMangoldt_div_sum_bounds hx
  have hup := prime_div_sum_le_vonMangoldt_sum x
  have hdown := vonMangoldt_sum_le_prime_div_sum hx
  change _ ≤ _ + B at hdown
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end AnalyticNumberTheory.Mertens
