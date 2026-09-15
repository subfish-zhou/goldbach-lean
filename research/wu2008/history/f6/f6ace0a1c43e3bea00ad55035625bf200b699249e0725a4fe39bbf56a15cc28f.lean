import MathlibNt.Wu2008DoubleSieve.GoldbachWeights
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The squareful error in Wu's lower weight

Wu (2004), Section 9, in the reduction to (9.3), removes nonsquarefree
sifted complements at cost `O(N^(1-κ))`; this is also needed for Wu (2008),
Lemma 2.1. We prove an explicit uniform bound without prime-density input:
there are at most `2*N/z` positive integers at most `N` divisible by a prime
square whose prime is at least `z`, for every real `z ≥ 2`.

The Goldbach specialization retains positivity and coprimality with `N`.
No claim about the totalized value of `Ω(0)` is used.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

/-- Positive integers with a prime-square divisor above a real cutoff. -/
noncomputable def largePrimeSquareExceptions (N : ℕ) (z : ℝ) : Finset ℕ :=
  (Ioc 0 N).filter (fun n => ∃ q : ℕ, q.Prime ∧ z ≤ (q : ℝ) ∧ q ^ 2 ∣ n)

theorem mem_largePrimeSquareExceptions {N n : ℕ} {z : ℝ} :
    n ∈ largePrimeSquareExceptions N z ↔
      0 < n ∧ n ≤ N ∧ ∃ q : ℕ, q.Prime ∧ z ≤ (q : ℝ) ∧ q ^ 2 ∣ n := by
  simp only [largePrimeSquareExceptions, mem_filter, mem_Ioc, and_assoc]

/-- The elementary telescoping majorant; no estimate for primes is used. -/
theorem reciprocal_square_le_difference {x : ℝ} (hx : 1 < x) :
    1 / x ^ 2 ≤ 1 / (x - 1) - 1 / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  calc
    1 / x ^ 2 ≤ 1 / (x * (x - 1)) :=
      one_div_le_one_div_of_le (mul_pos hx0 hx1) (by nlinarith)
    _ = 1 / (x - 1) - 1 / x := by
      field_simp
      ring

theorem sum_reciprocal_square_Icc_le (m N : ℕ) (hm : 2 ≤ m) :
    ∑ q ∈ Icc m N, (1 / (q : ℝ) ^ 2) ≤ 1 / ((m : ℝ) - 1) := by
  have hm' : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  by_cases hmN : m ≤ N
  · have ht := sum_Icc_sub hmN (fun q : ℕ => -(1 / ((q : ℝ) - 1)))
    have htel :
        ∑ q ∈ Icc m N, (1 / ((q : ℝ) - 1) - 1 / (q : ℝ)) =
          1 / ((m : ℝ) - 1) - 1 / (N : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
        neg_sub_neg] using ht
    calc
      ∑ q ∈ Icc m N, (1 / (q : ℝ) ^ 2) ≤
          ∑ q ∈ Icc m N, (1 / ((q : ℝ) - 1) - 1 / (q : ℝ)) := by
        apply sum_le_sum
        intro q hq
        apply reciprocal_square_le_difference
        exact hm'.trans_le (by exact_mod_cast (mem_Icc.mp hq).1)
      _ = 1 / ((m : ℝ) - 1) - 1 / (N : ℝ) := htel
      _ ≤ 1 / ((m : ℝ) - 1) := sub_le_self _ (by positivity)
  · rw [Icc_eq_empty_of_lt (by omega), sum_empty]
    positivity

/-- A finite union bound with the exact floor count of positive multiples. -/
theorem largePrimeSquareExceptions_card_le_sum (N : ℕ) (z : ℝ) :
    (largePrimeSquareExceptions N z).card ≤
      ∑ q ∈ Icc ⌈z⌉₊ N, N / q ^ 2 := by
  have hs : largePrimeSquareExceptions N z ⊆
      (Icc ⌈z⌉₊ N).biUnion (fun q => (Ioc 0 N).filter (fun n => q ^ 2 ∣ n)) := by
    intro n hn
    obtain ⟨hn0, hnN, q, _, hzq, hqn⟩ := mem_largePrimeSquareExceptions.mp hn
    have hqd : q ∣ n := dvd_trans (by simpa only [pow_two] using dvd_mul_right q q) hqn
    have hqN := (Nat.le_of_dvd hn0 hqd).trans hnN
    exact mem_biUnion.mpr ⟨q, mem_Icc.mpr ⟨Nat.ceil_le.mpr hzq, hqN⟩,
      mem_filter.mpr ⟨mem_Ioc.mpr ⟨hn0, hnN⟩, hqn⟩⟩
  calc
    (largePrimeSquareExceptions N z).card ≤
        ((Icc ⌈z⌉₊ N).biUnion
          (fun q => (Ioc 0 N).filter (fun n => q ^ 2 ∣ n))).card := card_le_card hs
    _ ≤ ∑ q ∈ Icc ⌈z⌉₊ N, ((Ioc 0 N).filter (fun n => q ^ 2 ∣ n)).card :=
      card_biUnion_le
    _ = ∑ q ∈ Icc ⌈z⌉₊ N, N / q ^ 2 := by
      simp only [Nat.Ioc_filter_dvd_card_eq_div]

theorem largePrimeSquareExceptions_card_le_ceiling (N : ℕ) {z : ℝ} (hz : 2 ≤ z) :
    ((largePrimeSquareExceptions N z).card : ℝ) ≤
      (N : ℝ) / ((⌈z⌉₊ : ℝ) - 1) := by
  have hm : 2 ≤ ⌈z⌉₊ := by
    exact_mod_cast hz.trans (Nat.le_ceil z)
  calc
    ((largePrimeSquareExceptions N z).card : ℝ) ≤
        ∑ q ∈ Icc ⌈z⌉₊ N, ((N / q ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast largePrimeSquareExceptions_card_le_sum N z
    _ ≤ ∑ q ∈ Icc ⌈z⌉₊ N, (N : ℝ) / (q : ℝ) ^ 2 := by
      apply sum_le_sum
      intro q _
      exact_mod_cast (Nat.cast_div_le (m := N) (n := q ^ 2) (α := ℝ))
    _ = (N : ℝ) * ∑ q ∈ Icc ⌈z⌉₊ N, (1 / (q : ℝ) ^ 2) := by
      rw [mul_sum]
      simp only [mul_one_div]
    _ ≤ (N : ℝ) * (1 / ((⌈z⌉₊ : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_square_Icc_le ⌈z⌉₊ N hm) (by positivity)
    _ = (N : ℝ) / ((⌈z⌉₊ : ℝ) - 1) := by ring

/-- Uniform in both the integer bound and the real cutoff, including `N = 0`. -/
theorem largePrimeSquareExceptions_card_le (N : ℕ) {z : ℝ} (hz : 2 ≤ z) :
    ((largePrimeSquareExceptions N z).card : ℝ) ≤ 2 * (N : ℝ) / z := by
  have hz0 : 0 < z := by linarith
  have hm : z ≤ (⌈z⌉₊ : ℝ) := Nat.le_ceil z
  have hm0 : 0 < (⌈z⌉₊ : ℝ) - 1 := by linarith
  calc
    ((largePrimeSquareExceptions N z).card : ℝ) ≤
        (N : ℝ) / ((⌈z⌉₊ : ℝ) - 1) := largePrimeSquareExceptions_card_le_ceiling N hz
    _ ≤ 2 * (N : ℝ) / z := by
      apply (div_le_div_iff₀ hm0 hz0).mpr
      nlinarith [show (0 : ℝ) ≤ N by positivity]

theorem largePrimeSquareExceptions_card_le_rpow {N : ℕ} {κ : ℝ}
    (hN : 0 < N) (hz : 2 ≤ (N : ℝ) ^ κ) :
    ((largePrimeSquareExceptions N ((N : ℝ) ^ κ)).card : ℝ) ≤
      2 * (N : ℝ) ^ (1 - κ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simpa only [Real.rpow_sub hN', Real.rpow_one, mul_div_assoc] using
    largePrimeSquareExceptions_card_le N hz

/-- A nonsquarefree coprime sifted positive integer has a large prime square. -/
theorem exists_large_prime_square_of_sifted_not_squarefree {M n : ℕ} {z : ℝ}
    (hcop : n.Coprime M) (hs : Sifted M n z) (hns : ¬Squarefree n) :
    ∃ q : ℕ, q.Prime ∧ z ≤ (q : ℝ) ∧ q ^ 2 ∣ n := by
  obtain ⟨q, hq, hqn⟩ : ∃ q : ℕ, q.Prime ∧ q * q ∣ n := by
    simpa only [Nat.squarefree_iff_prime_squarefree, not_forall,
      not_not, exists_prop] using hns
  have hqd : q ∣ n := dvd_trans (dvd_mul_right q q) hqn
  have hqM : q.Coprime M := hcop.of_dvd_left hqd
  refine ⟨q, hq, ?_, by simpa only [pow_two] using hqn⟩
  exact le_of_not_gt (fun hlt => hs q hq hqM hlt hqd)

/-- Actual prime indices of positive, coprime, sifted nonsquarefree complements. -/
noncomputable def squarefulSiftedGoldbach (N : ℕ) (z : ℝ) : Finset ℕ :=
  (sieveCarrier N 1 N z).filter
    (fun p => 0 < N - p ∧ (N - p).Coprime N ∧ ¬Squarefree (N - p))

theorem mem_squarefulSiftedGoldbach {N p : ℕ} {z : ℝ} :
    p ∈ squarefulSiftedGoldbach N z ↔
      p ≤ N ∧ p.Prime ∧ Sifted N (N - p) z ∧
        0 < N - p ∧ (N - p).Coprime N ∧ ¬Squarefree (N - p) := by
  simp only [squarefulSiftedGoldbach, sieveCarrier, mem_filter, mem_range,
    Nat.lt_succ_iff, one_dvd, Nat.div_one, true_and, and_assoc]

theorem squarefulSiftedGoldbach_card_le_largePrimeSquareExceptions (N : ℕ) (z : ℝ) :
    (squarefulSiftedGoldbach N z).card ≤ (largePrimeSquareExceptions N z).card := by
  apply card_le_card_of_injOn (fun p => N - p)
  · intro p hp
    obtain ⟨_, _, hs, hpos, hcop, hns⟩ := mem_squarefulSiftedGoldbach.mp hp
    exact mem_largePrimeSquareExceptions.mpr ⟨hpos, Nat.sub_le N p,
      exists_large_prime_square_of_sifted_not_squarefree hcop hs hns⟩
  · intro p hp q hq he
    change N - p = N - q at he
    have hpN := (mem_squarefulSiftedGoldbach.mp hp).1
    have hqN := (mem_squarefulSiftedGoldbach.mp hq).1
    omega

theorem squarefulSiftedGoldbach_card_le (N : ℕ) {z : ℝ} (hz : 2 ≤ z) :
    ((squarefulSiftedGoldbach N z).card : ℝ) ≤ 2 * (N : ℝ) / z := by
  calc
    ((squarefulSiftedGoldbach N z).card : ℝ) ≤
        ((largePrimeSquareExceptions N z).card : ℝ) := by
      exact_mod_cast squarefulSiftedGoldbach_card_le_largePrimeSquareExceptions N z
    _ ≤ 2 * (N : ℝ) / z := largePrimeSquareExceptions_card_le N hz

theorem squarefulSiftedGoldbach_card_le_rpow {N : ℕ} {κ : ℝ}
    (hN : 0 < N) (hz : 2 ≤ (N : ℝ) ^ κ) :
    ((squarefulSiftedGoldbach N ((N : ℝ) ^ κ)).card : ℝ) ≤
      2 * (N : ℝ) ^ (1 - κ) := by
  calc
    ((squarefulSiftedGoldbach N ((N : ℝ) ^ κ)).card : ℝ) ≤
        ((largePrimeSquareExceptions N ((N : ℝ) ^ κ)).card : ℝ) := by
      exact_mod_cast
        squarefulSiftedGoldbach_card_le_largePrimeSquareExceptions N ((N : ℝ) ^ κ)
    _ ≤ 2 * (N : ℝ) ^ (1 - κ) := largePrimeSquareExceptions_card_le_rpow hN hz

/-- The cutoff condition is proved eventually, not assumed as an analytic input. -/
theorem largePrimeSquareExceptions_eventually_le_rpow {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((largePrimeSquareExceptions N ((N : ℝ) ^ κ)).card : ℝ) ≤
        2 * (N : ℝ) ^ (1 - κ) := by
  have hz : ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ (N : ℝ) ^ κ :=
    ((tendsto_rpow_atTop hκ).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 2)
  filter_upwards [hz, Filter.eventually_ge_atTop (1 : ℕ)] with N hzN hN
  exact largePrimeSquareExceptions_card_le_rpow (by omega) hzN

theorem largePrimeSquareExceptions_isBigO {κ : ℝ} (hκ : 0 < κ) :
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ((largePrimeSquareExceptions N ((N : ℝ) ^ κ)).card : ℝ))
      (fun N : ℕ => (N : ℝ) ^ (1 - κ)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨2, ?_⟩
  filter_upwards [largePrimeSquareExceptions_eventually_le_rpow hκ] with N hN
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hN

/-- The actual coprime sifted Goldbach exceptions have the required power saving. -/
theorem squarefulSiftedGoldbach_isBigO {κ : ℝ} (hκ : 0 < κ) :
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ((squarefulSiftedGoldbach N ((N : ℝ) ^ κ)).card : ℝ))
      (fun N : ℕ => (N : ℝ) ^ (1 - κ)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨2, ?_⟩
  filter_upwards [largePrimeSquareExceptions_eventually_le_rpow hκ] with N hN
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  calc
    ((squarefulSiftedGoldbach N ((N : ℝ) ^ κ)).card : ℝ) ≤
        ((largePrimeSquareExceptions N ((N : ℝ) ^ κ)).card : ℝ) := by
      exact_mod_cast
        squarefulSiftedGoldbach_card_le_largePrimeSquareExceptions N ((N : ℝ) ^ κ)
    _ ≤ 2 * (N : ℝ) ^ (1 - κ) := hN

/-- Only a one-sided bound for the weight is needed; its absolute value
may be arbitrarily large. -/
theorem squarefulSiftedGoldbach_weight_sum_le (N : ℕ) {z : ℝ} (hz : 2 ≤ z)
    (w : ℕ → ℝ) (hw : ∀ p ∈ squarefulSiftedGoldbach N z, w p ≤ 2) :
    ∑ p ∈ squarefulSiftedGoldbach N z, w p ≤ 4 * (N : ℝ) / z := by
  calc
    ∑ p ∈ squarefulSiftedGoldbach N z, w p ≤
        ∑ _p ∈ squarefulSiftedGoldbach N z, (2 : ℝ) := sum_le_sum hw
    _ = 2 * ((squarefulSiftedGoldbach N z).card : ℝ) := by
      simp only [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ 2 * (2 * (N : ℝ) / z) :=
      mul_le_mul_of_nonneg_left (squarefulSiftedGoldbach_card_le N hz) (by norm_num)
    _ = 4 * (N : ℝ) / z := by ring

theorem squarefulSiftedGoldbach_weight_sum_le_rpow {N : ℕ} {κ : ℝ}
    (hN : 0 < N) (hz : 2 ≤ (N : ℝ) ^ κ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ squarefulSiftedGoldbach N ((N : ℝ) ^ κ), w p ≤ 2) :
    ∑ p ∈ squarefulSiftedGoldbach N ((N : ℝ) ^ κ), w p ≤
      4 * (N : ℝ) ^ (1 - κ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simpa only [Real.rpow_sub hN', Real.rpow_one, mul_div_assoc] using
    squarefulSiftedGoldbach_weight_sum_le N hz w hw

/-- Removing nonsquarefree terms from the actual positive coprime sifted
Goldbach sum costs at most `4*N/z` for any weight bounded above by two
on those terms. This is the one-sided squareful step in the lower weight. -/
theorem sifted_goldbach_sum_le_squarefree_sum_add (N : ℕ) {z : ℝ} (hz : 2 ≤ z)
    (w : ℕ → ℝ) (hw : ∀ p ∈ squarefulSiftedGoldbach N z, w p ≤ 2) :
    (∑ p ∈ (sieveCarrier N 1 N z).filter
        (fun p => 0 < N - p ∧ (N - p).Coprime N), w p) ≤
      (∑ p ∈ (sieveCarrier N 1 N z).filter
        (fun p => 0 < N - p ∧ (N - p).Coprime N ∧ Squarefree (N - p)), w p) +
        4 * (N : ℝ) / z := by
  have he := sum_filter_add_sum_filter_not
    ((sieveCarrier N 1 N z).filter (fun p => 0 < N - p ∧ (N - p).Coprime N))
    (fun p => Squarefree (N - p)) w
  simp only [filter_filter, and_assoc] at he
  have hb := squarefulSiftedGoldbach_weight_sum_le N hz w hw
  change (∑ p ∈ (sieveCarrier N 1 N z).filter
    (fun p => 0 < N - p ∧ (N - p).Coprime N ∧ ¬Squarefree (N - p)), w p) ≤ _ at hb
  linarith

end Wu2008DoubleSieve
