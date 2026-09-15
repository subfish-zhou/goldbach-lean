import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Inverse-totient mass of moduli divisible by large prime squares

These finite estimates concern the canonical mass `1 / φ(n)`, independently
of any sieve weight or choice of a well-factorable family.

The divisor identity `∑ d ∣ n, φ(d) = n` gives the majorant `τ(n) / n`;
enlarging the divisor-pair region to a square gives the bound `H(T)^2`.
Supermultiplicativity of the totient then handles each prime square, and a
finite inverse-square tail gives `4 H(T)^2 / u` for primes at least `u > 0`.
No assertion about the support or coefficients of a sieve family is used.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.PrimeSquareMass

open Finset
open scoped BigOperators

/-- The finite harmonic sum over positive integers at most `T`. -/
noncomputable def harmonicSum (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, (n : ℝ)⁻¹

/-- Positive moduli at most `T` with a repeated prime from `R`. -/
def badModuli (T : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (Icc 1 T).filter fun n => ∃ p ∈ R, p ^ 2 ∣ n

/-- Enlarging the quotient range bounds a nonnegative sum over multiples. -/
theorem sum_multiples_le (T d : ℕ) (hd : 0 < d)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ n ∈ (Icc 1 T).filter (d ∣ ·), f n ≤
      ∑ m ∈ Icc 1 T, f (d * m) := by
  have hsub : (Icc 1 T).filter (d ∣ ·) ⊆ (Icc 1 T).image (d * ·) := by
    intro n hn
    rcases mem_filter.mp hn with ⟨hn, m, rfl⟩
    rcases mem_Icc.mp hn with ⟨hn1, hnT⟩
    apply mem_image.mpr
    refine ⟨m, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · by_contra hm
      have : m = 0 := by omega
      simp [this] at hn1
    · exact (Nat.le_mul_of_pos_left m hd).trans hnT
  calc
    _ ≤ ∑ n ∈ (Icc 1 T).image (d * ·), f n :=
      sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)
    _ = _ := sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hd h)

/-- The divisor-count majorant for the inverse totient. -/
theorem inv_totient_le_divisor_sum (n : ℕ) (hn : 0 < n) :
    (n.totient : ℝ)⁻¹ ≤ ∑ _d ∈ n.divisors, (n : ℝ)⁻¹ := by
  have hφ : 0 < n.totient := Nat.totient_pos.mpr hn
  have h : n ≤ n.divisors.card * n.totient := by
    calc
      n = ∑ d ∈ n.divisors, d.totient := (Nat.sum_totient n).symm
      _ ≤ ∑ _d ∈ n.divisors, n.totient :=
        sum_le_sum fun d hd =>
          Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
      _ = _ := by simp
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hφR : 0 < (n.totient : ℝ) := by exact_mod_cast hφ
  have hR : (n : ℝ) ≤ (n.divisors.card : ℝ) * n.totient := by exact_mod_cast h
  simp only [sum_const, nsmul_eq_mul]
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hφR hnR]
  simpa using hR

/-- A finite, elementary mean bound, without an asymptotic constant. -/
theorem sum_inv_totient_le_harmonic_sq (T : ℕ) :
    ∑ n ∈ Icc 1 T, (n.totient : ℝ)⁻¹ ≤ harmonicSum T ^ 2 := by
  have hdiv (n : ℕ) (hn : n ∈ Icc 1 T) :
      n.divisors = (Icc 1 T).filter (· ∣ n) := by
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    rcases mem_Icc.mp hn with ⟨hn1, hnT⟩
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega),
        (Nat.le_of_dvd (by omega) hd).trans hnT⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, by omega⟩
  calc
    _ ≤ ∑ n ∈ Icc 1 T, ∑ _d ∈ n.divisors, (n : ℝ)⁻¹ :=
      sum_le_sum fun n hn => inv_totient_le_divisor_sum n (mem_Icc.mp hn).1
    _ = ∑ d ∈ Icc 1 T, ∑ n ∈ (Icc 1 T).filter (d ∣ ·), (n : ℝ)⁻¹ := by
      simp_rw [sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro n hn
      rw [hdiv n hn, sum_filter]
    _ ≤ ∑ d ∈ Icc 1 T, ∑ m ∈ Icc 1 T, ((d * m : ℕ) : ℝ)⁻¹ :=
      sum_le_sum fun d hd => sum_multiples_le T d (mem_Icc.mp hd).1
        (fun n => (n : ℝ)⁻¹) (fun n => by positivity)
    _ = harmonicSum T ^ 2 := by
      simp_rw [Nat.cast_mul, mul_inv, ← mul_sum]
      rw [← sum_mul, ← pow_two]
      rfl

/-- A fixed divisor costs at most its inverse totient in the finite mean bound. -/
theorem sum_inv_totient_multiples_le (T d : ℕ) (hd : 0 < d) :
    ∑ n ∈ (Icc 1 T).filter (d ∣ ·), (n.totient : ℝ)⁻¹ ≤
      (d.totient : ℝ)⁻¹ * harmonicSum T ^ 2 := by
  calc
    _ ≤ ∑ m ∈ Icc 1 T, ((d * m).totient : ℝ)⁻¹ :=
      sum_multiples_le T d hd (fun n => (n.totient : ℝ)⁻¹)
        (fun n => by positivity)
    _ ≤ ∑ m ∈ Icc 1 T, (d.totient : ℝ)⁻¹ * (m.totient : ℝ)⁻¹ := by
      apply sum_le_sum
      intro m hm
      have hdφ : (0 : ℝ) < d.totient := by
        exact_mod_cast Nat.totient_pos.mpr hd
      have hmφ : (0 : ℝ) < m.totient := by
        exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp hm).1
      have hmul : (d.totient : ℝ) * m.totient ≤ (d * m).totient := by
        exact_mod_cast Nat.totient_super_multiplicative d m
      simpa only [one_div, mul_inv] using
        one_div_le_one_div_of_le (mul_pos hdφ hmφ) hmul
    _ = (d.totient : ℝ)⁻¹ * ∑ m ∈ Icc 1 T, (m.totient : ℝ)⁻¹ :=
      (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_totient_le_harmonic_sq T)
      (by positivity)

/-- The union bound retains the sharper exact finite inverse-totient prime tail. -/
theorem badModuli_mass_le_totient_tail (T : ℕ) (R : Finset ℕ)
    (hR : ∀ p ∈ R, p.Prime) :
    ∑ n ∈ badModuli T R, (n.totient : ℝ)⁻¹ ≤
      (∑ p ∈ R, ((p ^ 2).totient : ℝ)⁻¹) * harmonicSum T ^ 2 := by
  calc
    _ = ∑ n ∈ Icc 1 T, if ∃ p ∈ R, p ^ 2 ∣ n then (n.totient : ℝ)⁻¹ else 0 :=
      sum_filter ..
    _ ≤ ∑ n ∈ Icc 1 T, ∑ p ∈ R, if p ^ 2 ∣ n then (n.totient : ℝ)⁻¹ else 0 := by
      apply sum_le_sum
      intro n _
      split_ifs with hn
      · obtain ⟨p, hp, hpn⟩ := hn
        have hsingle := single_le_sum (s := R) (a := p)
            (f := fun p => if p ^ 2 ∣ n then (n.totient : ℝ)⁻¹ else 0)
            (fun q _ => by split_ifs <;> positivity) hp
        rw [if_pos hpn] at hsingle
        exact hsingle
      · exact sum_nonneg fun p _ => by split_ifs <;> positivity
    _ = ∑ p ∈ R, ∑ n ∈ (Icc 1 T).filter (p ^ 2 ∣ ·), (n.totient : ℝ)⁻¹ := by
      rw [sum_comm]
      simp only [sum_filter]
    _ ≤ ∑ p ∈ R, ((p ^ 2).totient : ℝ)⁻¹ * harmonicSum T ^ 2 :=
      sum_le_sum fun p hp => sum_inv_totient_multiples_le T (p ^ 2)
        (pow_pos (hR p hp).pos _)
    _ = _ := (sum_mul ..).symm

theorem inv_totient_prime_sq_le {p : ℕ} (hp : p.Prime) :
    ((p ^ 2).totient : ℝ)⁻¹ ≤ 2 * ((p : ℝ) ^ 2)⁻¹ := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hφ : ((p ^ 2).totient : ℝ) = (p : ℝ) * (p - 1) := by
    rw [show p ^ 2 = p ^ (1 + 1) from rfl, Nat.totient_prime_pow_succ hp]
    simp only [pow_one, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hφpos : (0 : ℝ) < (p ^ 2).totient := by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos 2)
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hφpos (by positivity)]
  rw [hφ]
  nlinarith

/-- The explicit prime-square tail form of the bad-modulus mass estimate. -/
theorem badModuli_mass_le_prime_sq_tail (T : ℕ) (R : Finset ℕ)
    (hR : ∀ p ∈ R, p.Prime) :
    ∑ n ∈ badModuli T R, (n.totient : ℝ)⁻¹ ≤
      2 * (∑ p ∈ R, ((p : ℝ) ^ 2)⁻¹) * harmonicSum T ^ 2 := by
  refine (badModuli_mass_le_totient_tail T R hR).trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [mul_sum]
  exact sum_le_sum fun p hp => inv_totient_prime_sq_le (hR p hp)

/-- An inverse-square tail estimate for any finite set above a positive real cutoff. -/
theorem sum_inv_sq_le_of_lower_bound (R : Finset ℕ) (u : ℝ) (hu : 0 < u)
    (hR : ∀ p ∈ R, u ≤ p) :
    ∑ p ∈ R, ((p : ℝ) ^ 2)⁻¹ ≤ 2 / u := by
  have hc : 1 ≤ ⌈u⌉₊ := Nat.one_le_ceil_iff.mpr hu
  have hsub : R ⊆ Ioo (⌈u⌉₊ - 1) (R.sup id + 1) := by
    intro p hp
    have hlo : ⌈u⌉₊ ≤ p := Nat.ceil_le.mpr (hR p hp)
    have hhi : p ≤ R.sup id := le_sup (f := id) hp
    exact mem_Ioo.mpr ⟨by omega, by omega⟩
  have hcut : ((⌈u⌉₊ - 1 : ℕ) : ℝ) + 1 = (⌈u⌉₊ : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hc
  calc
    _ ≤ ∑ p ∈ Ioo (⌈u⌉₊ - 1) (R.sup id + 1), ((p : ℝ) ^ 2)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ ≤ 2 / (((⌈u⌉₊ - 1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le _ _
    _ = 2 / (⌈u⌉₊ : ℝ) := by rw [hcut]
    _ ≤ 2 / u := div_le_div_of_nonneg_left (by norm_num) hu (Nat.le_ceil u)

/-- Large repeated primes have total inverse-totient mass at most `4 H(T)^2 / u`. -/
theorem badModuli_mass_le_harmonic (T : ℕ) (R : Finset ℕ) (u : ℝ)
    (hu : 0 < u) (hprime : ∀ p ∈ R, p.Prime) (hlower : ∀ p ∈ R, u ≤ p) :
    ∑ n ∈ badModuli T R, (n.totient : ℝ)⁻¹ ≤
      (4 / u) * harmonicSum T ^ 2 := by
  calc
    _ ≤ 2 * (∑ p ∈ R, ((p : ℝ) ^ 2)⁻¹) * harmonicSum T ^ 2 :=
      badModuli_mass_le_prime_sq_tail T R hprime
    _ ≤ 2 * (2 / u) * harmonicSum T ^ 2 := by
      gcongr
      exact sum_inv_sq_le_of_lower_bound R u hu hlower
    _ = _ := by ring

theorem harmonicSum_nonneg (T : ℕ) : 0 ≤ harmonicSum T :=
  sum_nonneg fun n _ => by positivity

theorem harmonicSum_le_one_add_log (T : ℕ) :
    harmonicSum T ≤ 1 + Real.log T := by
  simpa only [harmonicSum, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast] using harmonic_le_one_add_log T

/-- The logarithmic form, valid also for `T = 0` under Lean's `log 0 = 0` convention. -/
theorem badModuli_mass_le_log (T : ℕ) (R : Finset ℕ) (u : ℝ)
    (hu : 0 < u) (hprime : ∀ p ∈ R, p.Prime) (hlower : ∀ p ∈ R, u ≤ p) :
    ∑ n ∈ badModuli T R, (n.totient : ℝ)⁻¹ ≤
      (4 / u) * (1 + Real.log T) ^ 2 := by
  refine (badModuli_mass_le_harmonic T R u hu hprime hlower).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (harmonicSum_nonneg T) (harmonicSum_le_one_add_log T) 2

#check sum_inv_totient_le_harmonic_sq
#print axioms sum_inv_totient_le_harmonic_sq
#check sum_inv_totient_multiples_le
#print axioms sum_inv_totient_multiples_le
#check badModuli_mass_le_totient_tail
#print axioms badModuli_mass_le_totient_tail
#check badModuli_mass_le_prime_sq_tail
#print axioms badModuli_mass_le_prime_sq_tail
#check sum_inv_sq_le_of_lower_bound
#print axioms sum_inv_sq_le_of_lower_bound
#check badModuli_mass_le_harmonic
#print axioms badModuli_mass_le_harmonic
#check harmonicSum_le_one_add_log
#print axioms harmonicSum_le_one_add_log
#check badModuli_mass_le_log
#print axioms badModuli_mass_le_log

end MathlibNt.SieveTheory.LiLiuPrereqWF.PrimeSquareMass
