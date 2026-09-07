import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGcdMean
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean
import Mathlib.Analysis.Real.Sqrt

/-!
# The beta-pair mass discarded at a large common divisor

Here the common divisor is `gcd(n₁, n₂)` of the two beta variables, not
`gcd(q, r)` of the moduli. The elementary gcd mean and the global second
divisor moment give an explicit inverse-square-root cutoff gain. No
arithmetic-progression, Siegel--Walfisz, or Shiu estimate is used.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

/-- Ordered pairs of beta indices whose common divisor exceeds a real cutoff. -/
def largeGCDPairs (N : Finset ℕ) (Y : ℝ) : Finset (ℕ × ℕ) :=
  (N ×ˢ N).filter (fun p => Y < (p.1.gcd p.2 : ℝ))

/-- The double gcd mean on any finite subset of the positive interval. -/
theorem sum_gcd_pairs_le_log {T : ℝ} (hT : 1 ≤ T)
    (N : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) :
    (∑ p ∈ N ×ˢ N, (p.1.gcd p.2 : ℝ)) ≤ T ^ 2 * (1 + Real.log T) := by
  have hT0 : 0 ≤ T := by linarith
  calc
    _ = ∑ n ∈ N, ∑ m ∈ N, (n.gcd m : ℝ) := sum_product _ _ _
    _ ≤ ∑ n ∈ N, T * (fouvryTau 2 n : ℝ) := by
      apply sum_le_sum
      intro n hn
      calc
        _ ≤ ∑ m ∈ Ioc 0 ⌊T⌋₊, (n.gcd m : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => by positivity)
        _ ≤ (⌊T⌋₊ : ℝ) * (n.divisors.card : ℝ) := by
          exact_mod_cast sum_gcd_le (mem_Ioc.mp (hN hn)).1.ne' ⌊T⌋₊
        _ ≤ T * (n.divisors.card : ℝ) :=
          mul_le_mul_of_nonneg_right (Nat.floor_le hT0) (by positivity)
        _ = _ := by rw [fouvryTau_two]
    _ = T * ∑ n ∈ N, (fouvryTau 2 n : ℝ) := (mul_sum _ _ _).symm
    _ ≤ T * ∑ n ∈ Ioc 0 ⌊T⌋₊, (fouvryTau 2 n : ℝ) :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => by positivity)) hT0
    _ ≤ T * (T * (1 + Real.log T)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa using sum_fouvryTau_le_real (k := 2) (by norm_num) hT) hT0
    _ = _ := by ring

/-- Markov's inequality for the large common divisor of the beta indices. -/
theorem card_largeGCDPairs_le {T Y : ℝ} (hT : 1 ≤ T) (hY : 0 < Y)
    (N : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) :
    ((largeGCDPairs N Y).card : ℝ) ≤ T ^ 2 * (1 + Real.log T) / Y := by
  apply (le_div_iff₀ hY).mpr
  calc
    _ = ∑ _p ∈ largeGCDPairs N Y, Y := by simp
    _ ≤ ∑ p ∈ largeGCDPairs N Y, (p.1.gcd p.2 : ℝ) := by
      apply sum_le_sum
      intro p hp
      exact (mem_filter.mp hp).2.le
    _ ≤ ∑ p ∈ N ×ˢ N, (p.1.gcd p.2 : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ _ := sum_gcd_pairs_le_log hT N hN

/-- Cauchy--Schwarz on any set of ordered pairs pays one coefficient square
sum and the square root of the number of retained pairs. -/
theorem sum_abs_pair_mul_le_sqrt_card {ι : Type*}
    (N : Finset ι) (S : Finset (ι × ι)) (hS : S ⊆ N ×ˢ N) (β : ι → ℝ) :
    (∑ p ∈ S, |β p.1 * β p.2|) ≤
      Real.sqrt (S.card : ℝ) * ∑ n ∈ N, β n ^ 2 := by
  have hsq :
      (∑ p ∈ S, (β p.1 * β p.2) ^ 2) ≤ (∑ n ∈ N, β n ^ 2) ^ 2 := by
    calc
      _ ≤ ∑ p ∈ N ×ˢ N, (β p.1 * β p.2) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => sq_nonneg _)
      _ = _ := by
        simp only [sum_product, pow_two, sum_mul_sum]
        apply sum_congr rfl
        intro n _
        apply sum_congr rfl
        intro m _
        ring
  calc
    _ ≤ Real.sqrt (S.card : ℝ) *
        Real.sqrt (∑ p ∈ S, (β p.1 * β p.2) ^ 2) := by
      simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, sq_abs] using
        Real.sum_mul_le_sqrt_mul_sqrt S (fun _ => (1 : ℝ)) (fun p => |β p.1 * β p.2|)
    _ ≤ Real.sqrt (S.card : ℝ) * Real.sqrt ((∑ n ∈ N, β n ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_sq (sum_nonneg (fun _ _ => sq_nonneg _))]

/-- Quantitative discarded beta-pair mass with inverse-square-root cutoff
gain, for arbitrary signed fixed-order divisor-bounded coefficients. -/
theorem sum_abs_largeGCDPairs_le {k : ℕ} (hk : 1 ≤ k) {T Y : ℝ}
    (hT : 1 ≤ T) (hY : 0 < Y)
    (N : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) (β : ℕ → ℝ)
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) :
    (∑ p ∈ largeGCDPairs N Y, |β p.1 * β p.2|) ≤
      T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
        Real.sqrt ((1 + Real.log T) / Y) := by
  have hT0 : 0 ≤ T := by linarith
  have hcard :
      Real.sqrt ((largeGCDPairs N Y).card : ℝ) ≤
        T * Real.sqrt ((1 + Real.log T) / Y) := by
    calc
      _ ≤ Real.sqrt (T ^ 2 * (1 + Real.log T) / Y) :=
        Real.sqrt_le_sqrt (card_largeGCDPairs_le hT hY N hN)
      _ = _ := by
        rw [mul_div_assoc, Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT0]
  calc
    _ ≤ Real.sqrt ((largeGCDPairs N Y).card : ℝ) * ∑ n ∈ N, β n ^ 2 :=
      sum_abs_pair_mul_le_sqrt_card N (largeGCDPairs N Y) (filter_subset _ _) β
    _ ≤ (T * Real.sqrt ((1 + Real.log T) / Y)) *
        (T * (1 + Real.log T) ^ (k ^ 2 - 1)) :=
      mul_le_mul hcard (sum_alpha_sq_le_fouvryTau hk hT N hN β hβ)
        (sum_nonneg (fun _ _ => sq_nonneg _)) (mul_nonneg hT0 (Real.sqrt_nonneg _))
    _ = _ := by ring

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
