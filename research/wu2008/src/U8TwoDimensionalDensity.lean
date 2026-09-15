import U8SmallPrefixLocalRoots
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! Actual local density for the original two-linear polynomial on small support.
The BoundingSieve below is used only for its quadratic algebra, not as a substitute
for the interval or its CRT remainder. -/
noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct.TwoDimensional

def roots (N p : ℕ) : ℝ := if p ∣ N then 1 else 2

def density (N : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => roots N p / p)

def term (N d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, roots N p / ((p : ℝ) - roots N p)

def carrier (Z R : ℝ) : Finset ℕ := by
  classical
  exact ((sievePrimes Z).prod id).divisors.filter fun d => (d : ℝ) ≤ R

def denominator (N : ℕ) (Z R : ℝ) : ℝ := ∑ d ∈ carrier Z R, term N d

theorem roots_pos (N p : ℕ) : 0 < roots N p := by
  unfold roots
  split_ifs <;> norm_num

theorem roots_le (N p : ℕ) : 1 ≤ roots N p := by
  unfold roots
  split_ifs <;> norm_num

theorem roots_lt {N p : ℕ} (hN : Even N) (hp : p.Prime) : roots N p < p := by
  unfold roots
  split_ifs with h
  · exact_mod_cast hp.one_lt
  · have hn : p ≠ 2 := fun he => h (he.symm ▸ hN.two_dvd)
    have : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hn)
    exact_mod_cast this

theorem density_prime (N : ℕ) {p : ℕ} (hp : p.Prime) :
    density N p = roots N p / p := by
  simp [density, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors]

theorem primorial_squarefree (Z : ℝ) : Squarefree ((sievePrimes Z).prod id) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => ?_) (fun p hp => (mem_sievePrimes.mp hp).1.squarefree)
  exact Nat.coprime_iff_isRelPrime.mp
    ((Nat.coprime_primes (mem_sievePrimes.mp hp).1 (mem_sievePrimes.mp hq).1).mpr hpq)

/-- Algebraic sieve with the genuine local density; its support is deliberately
empty because no interval approximation is assumed in this algebraic object. -/
def model (N : ℕ) (hN : Even N) (Z : ℝ) : BoundingSieve where
  support := ∅
  prodPrimes := (sievePrimes Z).prod id
  prodPrimes_squarefree := primorial_squarefree Z
  weights := fun _ => 0
  weights_nonneg := fun _ => le_rfl
  totalMass := 0
  nu := density N
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := by
    intro p hp _
    rw [density_prime N hp]
    exact div_pos (roots_pos N p) (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _
    rw [density_prime N hp]
    exact (div_lt_one (by exact_mod_cast hp.pos)).mpr (roots_lt hN hp)

theorem term_eq (N : ℕ) (hN : Even N) (Z : ℝ) {d : ℕ}
    (hd : d ∣ (sievePrimes Z).prod id) :
    (model N hN Z).selbergTerms d = term N d := by
  rw [BoundingSieve.selbergTerms_apply, ← (model N hN Z).prod_primeFactors_nu hd,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  change density N p * (1 - density N p)⁻¹ = _
  rw [density_prime N hp']
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  have hsub : (p : ℝ) - roots N p ≠ 0 := sub_ne_zero.mpr (roots_lt hN hp').ne'
  field_simp

theorem support_prime_not_dvd_pair {N p d : ℕ} {e R : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (hp : p.Prime) (hpd : p ∣ d) (hd : d ≠ 0)
    (hdR : (d : ℝ) ≤ R) (hR : R < (N : ℝ)^originalAlpha) : ¬p ∣ t.1*t.2 := by
  have hdata := pairs_data ht
  have hplt : (p : ℝ) < t.1 :=
    (show (p : ℝ) ≤ d by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hpd).trans_lt
      (hdR.trans_lt (hR.trans_le hdata.2.2.2.1))
  have hplt' : p < t.1 := by exact_mod_cast hplt
  have hplt2 : p < t.2 := hplt'.trans hdata.2.2.2.2.2.2.1
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · exact (ne_of_lt hplt') ((hdata.1.dvd_iff_eq hp.ne_one).mp h).symm
  · exact (ne_of_lt hplt2) ((hdata.2.1.dvd_iff_eq hp.ne_one).mp h).symm

theorem localRoots_eq_roots {N p d : ℕ} [Fact p.Prime] {e R : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (hpd : p ∣ d) (hd : d ≠ 0)
    (hdR : (d : ℝ) ≤ R) (hR : R < (N : ℝ)^originalAlpha) :
    ((localRoots p N (t.1*t.2)).card : ℝ) = roots N p := by
  have ha := support_prime_not_dvd_pair ht Fact.out hpd hd hdR hR
  unfold roots
  split_ifs with h
  · rw [localRoots_card_one_of_dvd_N ha h]
    norm_num
  · rw [localRoots_card_two ha h]
    norm_num

end U8Literal.SmallProduct.TwoDimensional
