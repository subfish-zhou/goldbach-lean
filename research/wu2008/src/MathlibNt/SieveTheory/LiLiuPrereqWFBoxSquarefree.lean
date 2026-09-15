import MathlibNt.SieveTheory.LiLiuPrereqWFDividedPowers

/-!
# Exact squarefree coefficients of the fixed divided-power box

The existing full-integer weight is not changed. On a squarefree integer
with `k` prime factors in the box, the raw slot sum is exactly `k!` and its
divided power is exactly one. This distinguishes a normalized aggregate
from its factorial-copy expansion; it asserts no sieve-density estimate.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open ArithmeticFunction Finset

theorem primeBox_pow_squarefree (B : Finset ℕ) (k : ℕ) {n : ℕ}
    (hn : Squarefree n) (hB : n.primeFactors ⊆ B)
    (hk : cardFactors n = k) :
    (primeBox B ^ k) n = k.factorial := by
  induction k generalizing n with
  | zero =>
      have hn1 : n = 1 :=
        (cardFactors_eq_zero_iff_eq_zero_or_one.mp hk).resolve_left hn.ne_zero
      simp [hn1]
  | succ k ih =>
      have hcard : n.primeFactors.card = k + 1 := by
        calc
          n.primeFactors.card = n.primeFactorsList.length :=
            List.toFinset_card_of_nodup
              ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn)
          _ = k + 1 := hk
      rw [pow_succ', primeBox_mul_apply]
      calc
        (∑ p ∈ n.primeFactors,
            if p ∈ B then (primeBox B ^ k) (n / p) else 0) =
          ∑ _p ∈ n.primeFactors, k.factorial := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [if_pos (hB hp)]
            have hd : n / p ∣ n :=
              ⟨p, (Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)).symm⟩
            apply ih (fun x hx => hn x (dvd_trans hx hd))
              ((Nat.primeFactors_mono hd hn.ne_zero).trans hB)
            have hcount := cardFactors_div_prime_add_one hp
            omega
        _ = (k + 1) * k.factorial := by simp [hcard]
        _ = (k + 1).factorial := (Nat.factorial_succ k).symm

/-- This is a theorem about the already fixed full-integer divided power,
not a squarefree mask substituted into its definition. -/
theorem boxWeight_squarefree_eq_one (B : Finset ℕ) (k : ℕ) {n : ℕ}
    (hn : Squarefree n) (hB : n.primeFactors ⊆ B)
    (hk : cardFactors n = k) :
    boxWeight B k n = 1 := by
  rw [boxWeight_apply, primeBox_pow_squarefree B k hn hB hk]
  exact div_self (by exact_mod_cast Nat.factorial_ne_zero k)

#check primeBox_pow_squarefree
#print axioms primeBox_pow_squarefree
#print axioms boxWeight_squarefree_eq_one

end MathlibNt.SieveTheory.LiLiuPrereqWF
