import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Goldbach local density

The Goldbach-type local density `ν(d) = ∏_{p | d} 1/(p-1)` used by additive
sieve problems such as Chen's theorem and the Goldbach conjecture.  On
squarefree moduli it is the reciprocal totient, which is the main term of the
Bombieri--Vinogradov distribution estimates.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real

/-- Goldbach local density: `ν(d) = ∏_{p | d} 1/(p-1)`. -/
noncomputable def goldbachNu : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun r => 1 / ((r : ℝ) - 1))

/-- The Goldbach density has the expected value on a prime. -/
theorem goldbachNu_apply_prime {p : ℕ} (hp : p.Prime) :
    goldbachNu p = 1 / ((p : ℝ) - 1) := by
  simp [goldbachNu, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,
    Nat.Prime.primeFactors hp]

/-- The Goldbach density is multiplicative. -/
theorem goldbachNu_isMultiplicative : goldbachNu.IsMultiplicative := by
  exact ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

/-- The Goldbach density is positive at every prime. -/
theorem goldbachNu_pos_of_prime {p : ℕ} (hp : p.Prime) : 0 < goldbachNu p := by
  rw [goldbachNu_apply_prime hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : 0 < (p : ℝ) - 1 := by linarith
  exact one_div_pos.mpr hden

/-- The Goldbach density is bounded by one at every prime larger than two. -/
theorem goldbachNu_lt_one_of_prime {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    goldbachNu p < 1 := by
  rw [goldbachNu_apply_prime hp]
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
  have hden_pos : 0 < (p : ℝ) - 1 := by linarith
  rw [div_lt_iff₀ hden_pos, one_mul]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  linarith

/-- The totient of a product of distinct primes is the product of their
shifted values. -/
private theorem totient_prod_eq_prod_sub_one (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    Nat.totient (∏ p ∈ S, p) = ∏ p ∈ S, (p - 1) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hp ih =>
      have hp' : p.Prime := hS p (Finset.mem_insert_self _ _)
      have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (∏ q ∈ S, q) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        exact (Nat.coprime_primes hp' (hS' q hq)).mpr (by
          intro hpq
          subst q
          exact hp hq)
      calc
        Nat.totient (∏ x ∈ insert p S, x)
            = Nat.totient (p * ∏ q ∈ S, q) := by rw [Finset.prod_insert hp]
        _ = Nat.totient p * Nat.totient (∏ q ∈ S, q) := by rw [Nat.totient_mul hcop]
        _ = (p - 1) * ∏ q ∈ S, (q - 1) := by rw [Nat.totient_prime hp', ih hS']
        _ = ∏ q ∈ insert p S, (q - 1) := by rw [Finset.prod_insert hp]

/-- The totient of a squarefree natural is the product of `p - 1` over its
prime factors. -/
theorem totient_eq_prod_primeFactors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact not_squarefree_zero hn
  have hprod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
    Nat.prod_primeFactors_pow_factorization hn0
  have hsq : ∀ p ∈ n.primeFactors, n.factorization p = 1 := by
    intro p hp
    exact Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  have hpow : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = ∏ p ∈ n.primeFactors, p := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [hsq p hp, pow_one]
  have hφ : Nat.totient n = Nat.totient (∏ p ∈ n.primeFactors, p ^ n.factorization p) := by
    exact congrArg Nat.totient hprod
  calc
    Nat.totient n = Nat.totient (∏ p ∈ n.primeFactors, p ^ n.factorization p) := hφ
    _ = Nat.totient (∏ p ∈ n.primeFactors, p) := congrArg Nat.totient hpow
    _ = ∏ p ∈ n.primeFactors, (p - 1) :=
      totient_prod_eq_prod_sub_one n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)

/-- The Goldbach density of a squarefree modulus is exactly the reciprocal
totient: `ν(d) = 1/φ(d)`.  This identifies the distribution main term
`ν(d) · x/log x` with the standard Bombieri--Vinogradov main term
`li(x)/φ(d)`. -/
theorem goldbachNu_squarefree_eq_inv_totient {d : ℕ} (hd : Squarefree d) :
    goldbachNu d = (1 : ℝ) / (Nat.totient d : ℝ) := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact not_squarefree_zero hd
  have hnu : goldbachNu d = ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) := by
    unfold goldbachNu
    rw [ArithmeticFunction.prodPrimeFactors_apply hd0]
  rw [hnu]
  have htot_nat : Nat.totient d = ∏ p ∈ d.primeFactors, (p - 1) :=
    totient_eq_prod_primeFactors_of_squarefree hd
  rw [htot_nat]
  simp_rw [Nat.cast_prod]
  simp_rw [one_div]
  rw [Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hp1 : (1 : ℕ) ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
  rw [Nat.cast_sub hp1]
  norm_num

end AnalyticNumberTheory.Sieve
