import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The actual finite sieve-divisor support

The convention is strictly `p < z`: `siftingProduct N z` is the natural-number
product of precisely the primes below the real cutoff `z` which do not divide
`N`. In particular 2 is excluded only when it divides `N`. The ceiling in the
finite carrier implements this strict real cutoff, including integral cutoffs.

These elementary support facts use the frozen Mathlib prime-product,
coprimality, and squarefreeness lemmas. They do not import a density product or
the corrected Chen product (which additionally excludes 2 and fixes its cutoff).
No distribution estimate or indexed prime-pair carrier is asserted here.
-/

namespace Wu2004MeanValue

open Finset
open scoped BigOperators

noncomputable section

/-- The primes `p < z` with `p ∤ N`, with the canonical strict cutoff. -/
def siftingPrimes (N : ℕ) (z : ℝ) : Finset ℕ :=
  (range ⌈z⌉₊).filter (fun p => p.Prime ∧ ¬p ∣ N)

/-- The actual natural-number product `P_N(z)`, not a density product. -/
def siftingProduct (N : ℕ) (z : ℝ) : ℕ :=
  ∏ p ∈ siftingPrimes N z, p

/-- Only divisors of the actual sieve product, at the finite modulus level. -/
def sieveModuli (N : ℕ) (z : ℝ) (Q : ℕ) : Finset ℕ :=
  (Icc 1 Q).filter (fun d => d ∣ siftingProduct N z)

@[simp]
theorem mem_siftingPrimes {N p : ℕ} {z : ℝ} :
    p ∈ siftingPrimes N z ↔ (p : ℝ) < z ∧ p.Prime ∧ ¬p ∣ N := by
  simp only [siftingPrimes, mem_filter, mem_range, Nat.lt_ceil]

@[simp]
theorem mem_sieveModuli {N Q d : ℕ} {z : ℝ} :
    d ∈ sieveModuli N z Q ↔ 1 ≤ d ∧ d ≤ Q ∧ d ∣ siftingProduct N z := by
  simp only [sieveModuli, mem_filter, mem_Icc, and_assoc]

theorem sieveModuli_subset_Icc (N : ℕ) (z : ℝ) (Q : ℕ) :
    sieveModuli N z Q ⊆ Icc 1 Q :=
  filter_subset _ _

theorem siftingProduct_pos (N : ℕ) (z : ℝ) :
    0 < siftingProduct N z := by
  exact prod_pos fun p hp => (mem_siftingPrimes.mp hp).2.1.pos

theorem siftingProduct_ne_zero (N : ℕ) (z : ℝ) :
    siftingProduct N z ≠ 0 :=
  (siftingProduct_pos N z).ne'

/-- Exact prime-factor characterization, including the exclusion of factors of `N`. -/
theorem prime_dvd_siftingProduct_iff {N p : ℕ} {z : ℝ} (hp : p.Prime) :
    p ∣ siftingProduct N z ↔ (p : ℝ) < z ∧ ¬p ∣ N := by
  constructor
  · intro h
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp h
    have hq' := mem_siftingPrimes.mp hq
    have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq'.2.1).mp hpq
    subst q
    exact ⟨hq'.1, hq'.2.2⟩
  · intro h
    exact dvd_prod_of_mem _ (mem_siftingPrimes.mpr ⟨h.1, hp, h.2⟩)

theorem siftingProduct_squarefree (N : ℕ) (z : ℝ) :
    Squarefree (siftingProduct N z) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (mem_siftingPrimes.mp hp).2.1
        (mem_siftingPrimes.mp hq).2.1).mpr hpq)
  · intro p hp
    exact (mem_siftingPrimes.mp hp).2.1.squarefree

theorem coprime_siftingProduct (N : ℕ) (z : ℝ) :
    N.Coprime (siftingProduct N z) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  have hp' := mem_siftingPrimes.mp hp
  exact (hp'.2.1.coprime_iff_not_dvd.mpr hp'.2.2).symm

/-- This needs no coprimality assumption for arbitrary moduli below `Q`. -/
theorem coprime_of_mem_sieveModuli {N Q d : ℕ} {z : ℝ}
    (hd : d ∈ sieveModuli N z Q) : N.Coprime d :=
  (coprime_siftingProduct N z).coprime_dvd_right (mem_sieveModuli.mp hd).2.2

theorem squarefree_of_mem_sieveModuli {N Q d : ℕ} {z : ℝ}
    (hd : d ∈ sieveModuli N z Q) : Squarefree d :=
  (siftingProduct_squarefree N z).squarefree_of_dvd (mem_sieveModuli.mp hd).2.2

/-- Equality at the cutoff is permitted because the product uses `p < z`. -/
theorem prime_not_dvd_siftingProduct {N r : ℕ} {z : ℝ}
    (hr : r.Prime) (hz : z ≤ (r : ℝ)) : ¬r ∣ siftingProduct N z := by
  intro h
  exact (not_lt_of_ge hz) ((prime_dvd_siftingProduct_iff hr).mp h).1

theorem prime_coprime_siftingProduct {N r : ℕ} {z : ℝ}
    (hr : r.Prime) (hz : z ≤ (r : ℝ)) : r.Coprime (siftingProduct N z) :=
  hr.coprime_iff_not_dvd.mpr (prime_not_dvd_siftingProduct hr hz)

theorem prime_not_dvd_of_mem_sieveModuli {N Q d r : ℕ} {z : ℝ}
    (hd : d ∈ sieveModuli N z Q) (hr : r.Prime) (hz : z ≤ (r : ℝ)) :
    ¬r ∣ d := by
  intro h
  exact prime_not_dvd_siftingProduct hr hz
    (dvd_trans h (mem_sieveModuli.mp hd).2.2)

theorem prime_coprime_of_mem_sieveModuli {N Q d r : ℕ} {z : ℝ}
    (hd : d ∈ sieveModuli N z Q) (hr : r.Prime) (hz : z ≤ (r : ℝ)) :
    r.Coprime d :=
  hr.coprime_iff_not_dvd.mpr (prime_not_dvd_of_mem_sieveModuli hd hr hz)

/-- The omitted common-main correction vanishes exactly, with no estimate on `L`. -/
theorem omitted_main_sum_eq_zero {α : Type*} [AddCommMonoid α]
    {N Q d : ℕ} {z : ℝ} (hd : d ∈ sieveModuli N z Q)
    (S : Finset ℕ) (L : ℕ → α)
    (hS : ∀ r ∈ S, r.Prime ∧ z ≤ (r : ℝ)) :
    (∑ r ∈ S with r ∣ d, L r) = 0 := by
  apply sum_eq_zero
  intro r hr
  obtain ⟨hrS, hrd⟩ := mem_filter.mp hr
  exact False.elim
    (prime_not_dvd_of_mem_sieveModuli hd (hS r hrS).1 (hS r hrS).2 hrd)

/-- The strict separation supplied by the manuscript's cutoff estimates. -/
theorem omitted_main_sum_eq_zero_of_lt {α : Type*} [AddCommMonoid α]
    {N Q d : ℕ} {z : ℝ} (hd : d ∈ sieveModuli N z Q)
    (S : Finset ℕ) (L : ℕ → α)
    (hS : ∀ r ∈ S, r.Prime ∧ z < (r : ℝ)) :
    (∑ r ∈ S with r ∣ d, L r) = 0 :=
  omitted_main_sum_eq_zero hd S L fun r hr => ⟨(hS r hr).1, (hS r hr).2.le⟩

/-- On the actual sieve support the coprimality-gated main sum is the full sum. -/
theorem coprime_main_sum_eq_sum {α : Type*} [AddCommMonoid α]
    {N Q d : ℕ} {z : ℝ} (hd : d ∈ sieveModuli N z Q)
    (S : Finset ℕ) (L : ℕ → α)
    (hS : ∀ r ∈ S, r.Prime ∧ z ≤ (r : ℝ)) :
    (∑ r ∈ S with r.Coprime d, L r) = ∑ r ∈ S, L r := by
  have hfilter : S.filter (fun r => r.Coprime d) = S := by
    apply filter_eq_self.mpr
    intro r hr
    exact prime_coprime_of_mem_sieveModuli hd (hS r hr).1 (hS r hr).2
  rw [hfilter]

end
end Wu2004MeanValue
