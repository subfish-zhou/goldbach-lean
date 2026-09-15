import MathlibNt.Wu2008DoubleSieve.LowerWeightSum

/-!
# Uniform multiplicity budgets for closed-sifting endpoints

Distinct prime divisors above `N^κ` have cardinality at most `1/κ`.
This applies to every positive integer at most `N`, without squarefreeness
or coprimality assumptions.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def largePrimeDivisors (n : ℕ) (z : ℝ) : Finset ℕ :=
  n.primeFactors.filter (fun q => z ≤ (q : ℝ))

theorem mem_largePrimeDivisors {n q : ℕ} {z : ℝ} :
    q ∈ largePrimeDivisors n z ↔
      q.Prime ∧ q ∣ n ∧ n ≠ 0 ∧ z ≤ (q : ℝ) := by
  simp only [largePrimeDivisors, mem_filter, Nat.mem_primeFactors, and_assoc]

theorem largePrimeDivisors_pow_card_le {n : ℕ} (hn : 0 < n)
    {z : ℝ} (hz : 0 ≤ z) :
    z ^ (largePrimeDivisors n z).card ≤ (n : ℝ) := by
  have hd : (∏ q ∈ largePrimeDivisors n z, q) ∣ n :=
    (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd n)
  calc
    z ^ (largePrimeDivisors n z).card =
        ∏ _q ∈ largePrimeDivisors n z, z := (prod_const z).symm
    _ ≤ ∏ q ∈ largePrimeDivisors n z, (q : ℝ) := by
      apply prod_le_prod (fun _ _ => hz)
      intro q hq
      exact (mem_largePrimeDivisors.mp hq).2.2.2
    _ = ((∏ q ∈ largePrimeDivisors n z, q : ℕ) : ℝ) := by
      simp only [Nat.cast_prod]
    _ ≤ n := by exact_mod_cast Nat.le_of_dvd hn hd

theorem largePrimeDivisors_card_le_inv {N n : ℕ} (hN : 1 < N)
    (hn : 0 < n) (hnN : n ≤ N) {κ : ℝ} (hκ : 0 < κ) :
    ((largePrimeDivisors n ((N : ℝ) ^ κ)).card : ℝ) ≤ 1 / κ := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  have hp := largePrimeDivisors_pow_card_le hn
    (Real.rpow_nonneg (Nat.cast_nonneg N) κ)
  have hle :
      (N : ℝ) ^ (κ * (largePrimeDivisors n ((N : ℝ) ^ κ)).card) ≤
        (N : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_mul (Nat.cast_nonneg N), Real.rpow_natCast, Real.rpow_one]
    exact hp.trans (by exact_mod_cast hnN)
  have he := (Real.rpow_le_rpow_left_iff hN').mp hle
  apply (le_div_iff₀ hκ).mpr
  nlinarith

/-- Zero complements are absent on the source's even Goldbach carrier. -/
theorem complement_pos_of_even {N p : ℕ} (hN : 4 ≤ N) (he : Even N)
    (hpN : p ≤ N) (hp : p.Prime) : 0 < N - p := by
  have hpne : p ≠ N := by
    intro h
    subst p
    have htwo := hp.even_iff.mp he
    omega
  omega

end Wu2008DoubleSieve
