import MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier

open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Every actual S2 large prime is coprime to every divisor of the standard
sieving-prime product at a cutoff at most N^(1/4). No gate-loss estimate is
needed on this support. This does not yet construct the switched sieve. -/
theorem goldbachS2_sieveDivisor_coprime
    (N : ℕ) {ε Z : ℝ} (hN : 1 ≤ N) (hεu : ε < (2 : ℝ) / 15)
    {r d : ℕ}
    (hr : r ∈ goldbachS2Primes N ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)))
    (hZ : Z ≤ (N : ℝ) ^ ((1 : ℝ) / 4))
    (hd : d ∣ goldbachS1ProdPrimes N Z) : Nat.Coprime r d := by
  rcases (Finset.mem_filter.mp hr).2 with ⟨hrp, _hrN, hrT, _hrSq⟩
  have hτ : (1 : ℝ) / 4 ≤ (9 : ℝ) / 19 - ε := by linarith
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlarge : Z ≤ (r : ℝ) :=
    hZ.trans ((Real.rpow_le_rpow_of_exponent_le hbase hτ).trans hrT)
  apply hrp.coprime_iff_not_dvd.mpr
  intro hrd
  have hsmall : (r : ℝ) < Z :=
    ((prime_dvd_goldbachS1ProdPrimes_iff hrp).mp (hrd.trans hd)).1
  exact (not_lt_of_ge hlarge) hsmall

/-- The actual large-prime main sum has no coprimality deletion on these
sieving divisors, for any real mass attached to each large prime. -/
theorem goldbachS2_gated_sum_eq_sum
    (N : ℕ) {ε Z : ℝ} (hN : 1 ≤ N) (hεu : ε < (2 : ℝ) / 15)
    {d : ℕ} (hZ : Z ≤ (N : ℝ) ^ ((1 : ℝ) / 4))
    (hd : d ∣ goldbachS1ProdPrimes N Z) (w : ℕ → ℝ) :
    (∑ r ∈ goldbachS2Primes N ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)),
      if Nat.Coprime r d then w r else 0) =
    ∑ r ∈ goldbachS2Primes N ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)), w r := by
  apply Finset.sum_congr rfl
  intro r hr
  rw [if_pos (goldbachS2_sieveDivisor_coprime N hN hεu hr hZ hd)]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig