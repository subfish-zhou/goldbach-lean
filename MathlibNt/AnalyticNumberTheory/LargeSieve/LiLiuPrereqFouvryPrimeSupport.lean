import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated

/-!
# Canonical prime-support splitting

Separate the full prime powers in `n` according to whether their primes divide `d`.
These are the `d`-infinity factors used in Fouvry (1984), pp. 235–236.
The definitions are total; reconstruction requires only `0 < n`.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open scoped BigOperators

/-- The factor of `n` containing the full powers of primes dividing `d`. -/
def supportedPart (n d : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ∣ d), p ^ n.factorization p

/-- The complementary factor of `n`, containing primes not dividing `d`. -/
def coprimePart (n d : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => ¬p ∣ d), p ^ n.factorization p

theorem supportedPart_pos (n d : ℕ) : 0 < supportedPart n d := by
  apply Nat.pos_of_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

theorem coprimePart_pos (n d : ℕ) : 0 < coprimePart n d := by
  apply Nat.pos_of_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

theorem supportedPart_mul_coprimePart {n : ℕ} (hn : 0 < n) (d : ℕ) :
    supportedPart n d * coprimePart n d = n := by
  rw [supportedPart, coprimePart, Finset.prod_filter_mul_prod_filter_not]
  exact (Nat.prod_primeFactors_pow_factorization (Nat.ne_of_gt hn)).symm

theorem supportedPart_dvd {n : ℕ} (hn : 0 < n) (d : ℕ) :
    supportedPart n d ∣ n :=
  ⟨coprimePart n d, (supportedPart_mul_coprimePart hn d).symm⟩


/-- Every prime divisor of the supported part divides the reference integer. -/
theorem prime_dvd_supportedPart {n d p : ℕ} (hp : p.Prime)
    (hps : p ∣ supportedPart n d) : p ∣ d := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hps
  obtain ⟨hqn, hqd⟩ := Finset.mem_filter.mp hq
  have heq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hqn)).mp
      (hp.dvd_of_dvd_pow hpq)
  exact heq ▸ hqd

/-- Every prime divisor of the complementary part avoids the reference integer. -/
theorem prime_dvd_coprimePart_not_dvd {n d p : ℕ} (hp : p.Prime)
    (hpt : p ∣ coprimePart n d) : ¬p ∣ d := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpt
  obtain ⟨hqn, hqd⟩ := Finset.mem_filter.mp hq
  have heq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hqn)).mp
      (hp.dvd_of_dvd_pow hpq)
  exact heq ▸ hqd

theorem coprimePart_coprime (n d : ℕ) : (coprimePart n d).Coprime d := by
  by_contra h
  obtain ⟨p, hp, hpt, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact prime_dvd_coprimePart_not_dvd hp hpt hpd

/-- Coprimality transfers from `d` to every integer supported on primes dividing `d`. -/
theorem coprime_of_prime_support {u d s : ℕ} (hu : u.Coprime d)
    (hs : ∀ p : ℕ, p.Prime → p ∣ s → p ∣ d) : u.Coprime s := by
  by_contra h
  obtain ⟨p, hp, hpu, hps⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpu, hs p hp hps⟩) hu


/-- Every supported divisor of `n` divides its canonical supported part. -/
theorem dvd_supportedPart_of_prime_support {n d s : ℕ} (hn : 0 < n)
    (hsn : s ∣ n) (hs : ∀ p : ℕ, p.Prime → p ∣ s → p ∣ d) :
    s ∣ supportedPart n d := by
  have hst : s.Coprime (coprimePart n d) :=
    (coprime_of_prime_support (coprimePart_coprime n d) hs).symm
  apply hst.dvd_mul_right.mp
  rwa [supportedPart_mul_coprimePart hn d]


/-- The prime-support conditions determine both factors, including unit factors. -/
theorem prime_support_split_unique {n d s t : ℕ} (hn : 0 < n)
    (hst : s * t = n) (hs : ∀ p : ℕ, p.Prime → p ∣ s → p ∣ d)
    (ht : t.Coprime d) : s = supportedPart n d ∧ t = coprimePart n d := by
  have hs_le : s ∣ supportedPart n d :=
    dvd_supportedPart_of_prime_support hn ⟨t, hst.symm⟩ hs
  have hsc : (supportedPart n d).Coprime t :=
    (coprime_of_prime_support ht
      (fun _ hp hps => prime_dvd_supportedPart hp hps)).symm
  have hs_ge : supportedPart n d ∣ s := by
    apply hsc.dvd_mul_right.mp
    rw [hst]
    exact supportedPart_dvd hn d
  have hs_eq : s = supportedPart n d := Nat.dvd_antisymm hs_le hs_ge
  refine ⟨hs_eq, ?_⟩
  apply Nat.mul_left_cancel (supportedPart_pos n d)
  rw [supportedPart_mul_coprimePart hn d, ← hs_eq]
  exact hst


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
