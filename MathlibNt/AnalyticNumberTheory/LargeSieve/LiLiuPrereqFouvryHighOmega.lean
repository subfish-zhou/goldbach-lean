import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanError

/-!
# Exponential saving from high distinct-prime-factor beta support

The cutoff is real. The elementary Rankin weight is `2 ^ omega(n)`;
its absorption only doubles the fixed divisor order, with no power of the
ambient scale lost.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def betaLowOmega (β : ℕ → ℝ) (ξ : ℝ) (n : ℕ) : ℝ :=
  if (n.primeFactors.card : ℝ) ≤ ξ then β n else 0

def betaHighOmega (β : ℕ → ℝ) (ξ : ℝ) (n : ℕ) : ℝ :=
  if ξ < (n.primeFactors.card : ℝ) then β n else 0

theorem beta_eq_lowOmega_add_highOmega (β : ℕ → ℝ) (ξ : ℝ) (n : ℕ) :
    β n = betaLowOmega β ξ n + betaHighOmega β ξ n := by
  unfold betaLowOmega betaHighOmega
  by_cases h : (n.primeFactors.card : ℝ) ≤ ξ
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

theorem abs_betaLowOmega_le (β : ℕ → ℝ) (ξ : ℝ) (n : ℕ) :
    |betaLowOmega β ξ n| ≤ |β n| := by
  unfold betaLowOmega
  split_ifs <;> simp

theorem abs_betaHighOmega_le (β : ℕ → ℝ) (ξ : ℝ) (n : ℕ) :
    |betaHighOmega β ξ n| ≤ |β n| := by
  unfold betaHighOmega
  split_ifs <;> simp

theorem betaLowOmega_nonzero_card_le {β : ℕ → ℝ} {ξ : ℝ} {n : ℕ}
    (h : betaLowOmega β ξ n ≠ 0) : (n.primeFactors.card : ℝ) ≤ ξ := by
  by_contra hh
  exact h (if_neg hh)

theorem two_pow_card_primeFactors_le_tau {n : ℕ} (hn : n ≠ 0) :
    2 ^ n.primeFactors.card ≤ fouvryTau 2 n := by
  rw [fouvryTau_two, Nat.card_divisors hn, ← prod_const]
  apply prod_le_prod'
  intro p hp
  have hp' : n.factorization p ≠ 0 := by
    exact Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization])
  omega

theorem highOmega_rankin_bound (k : ℕ) {n : ℕ} (hn : n ≠ 0)
    {ξ : ℝ} (hξ : ξ < (n.primeFactors.card : ℝ)) :
    (fouvryTau k n : ℝ) ≤ (2 : ℝ) ^ (-ξ) * fouvryTau (2 * k) n := by
  have ht : (2 : ℝ) ^ ξ ≤ (fouvryTau 2 n : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ (n.primeFactors.card : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hξ.le
      _ = ((2 ^ n.primeFactors.card : ℕ) : ℝ) := by
        rw [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ _ := by exact_mod_cast two_pow_card_primeFactors_le_tau hn
  have hmul : (2 : ℝ) ^ ξ * fouvryTau k n ≤ (fouvryTau (2 * k) n : ℝ) :=
    (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _)).trans
      (by exact_mod_cast fouvryTau_mul_le 2 k n)
  have hpow : (2 : ℝ) ^ (-ξ) * (2 : ℝ) ^ ξ = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  have := mul_le_mul_of_nonneg_left hmul
    (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (-ξ))
  simpa only [← mul_assoc, hpow, one_mul] using this

theorem abs_betaHighOmega_le_rankin (k : ℕ) {N : Finset ℕ}
    {β : ℕ → ℝ} (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (ξ : ℝ) {n : ℕ} (hn : n ∈ N) :
    |betaHighOmega β ξ n| ≤ (2 : ℝ) ^ (-ξ) * fouvryTau (2 * k) n := by
  obtain rfl | hn0 := eq_or_ne n 0
  · have := hβ 0 hn
    have hβ0 : β 0 = 0 := abs_eq_zero.mp (le_antisymm (by simpa using this) (abs_nonneg _))
    simp [betaHighOmega, hβ0]
  unfold betaHighOmega
  split_ifs with hξ
  · exact (hβ n hn).trans (highOmega_rankin_bound k hn0 hξ)
  · simp only [abs_zero]
    positivity

/-- A convenient all-orders global mean; increasing the order by one
also treats order zero without exceptional cases. -/
theorem highOmega_sum_tau_le (k : ℕ) {x : ℝ} (hx : 1 ≤ x)
    (N : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊x⌋₊) :
    (∑ n ∈ N, (fouvryTau k n : ℝ)) ≤ x * (1 + Real.log x) ^ k := by
  calc
    _ ≤ ∑ n ∈ N, (fouvryTau (k + 1) n : ℝ) :=
      sum_le_sum (fun n _ => by exact_mod_cast fouvryTau_le_succ k n)
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau (k + 1) n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ _ := by simpa using sum_fouvryTau_le_real (k := k + 1) (by omega) hx

theorem sum_abs_betaHighOmega_le (k : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (N : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) (β : ℕ → ℝ)
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) (ξ : ℝ) :
    (∑ n ∈ N, |betaHighOmega β ξ n|) ≤
      (2 : ℝ) ^ (-ξ) * T * (1 + Real.log T) ^ (2 * k) := by
  calc
    _ ≤ ∑ n ∈ N, (2 : ℝ) ^ (-ξ) * fouvryTau (2 * k) n :=
      sum_le_sum (fun _ hn => abs_betaHighOmega_le_rankin k hβ ξ hn)
    _ = (2 : ℝ) ^ (-ξ) * ∑ n ∈ N, (fouvryTau (2 * k) n : ℝ) := (mul_sum ..).symm
    _ ≤ (2 : ℝ) ^ (-ξ) * (T * (1 + Real.log T) ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left (highOmega_sum_tau_le (2 * k) hT N hN)
        (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
