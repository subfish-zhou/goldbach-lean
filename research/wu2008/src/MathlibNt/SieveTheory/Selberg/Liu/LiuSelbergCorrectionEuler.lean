import Mathlib.NumberTheory.EulerProduct.Basic
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergDenominatorConvolution
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

/-!
# Euler total of Liu's Selberg correction

This file proves absolute summability of the correction in the exact
denominator convolution and identifies its signed Euler total.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Finset
open Filter
open MathlibNt.SieveTheory.SingularSeries

noncomputable def liuSelbergAbsPrimeDeviation (N : ℕ) (p : Nat.Primes) : ℝ :=
  (∑' e : ℕ, |liuSelbergCorrection N ((p : ℕ) ^ e)|) - 1

theorem summable_abs_liuSelbergCorrection_prime_pow
    (N : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ => |liuSelbergCorrection N (p ^ e)|) := by
  by_cases hpn : p ∣ N
  · apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro e he
    have he2 : 2 ≤ e := Nat.le_of_not_gt (by simpa using he)
    rw [liuSelbergCorrection_prime_pow_eq_zero_of_dvd hp hpn he2]
    simp
  · apply summable_of_ne_finset_zero (s := Finset.range 3)
    intro e he
    have he3 : 3 ≤ e := Nat.le_of_not_gt (by simpa using he)
    rw [liuSelbergCorrection_prime_pow_eq_zero_of_not_dvd hp hpn he3]
    simp

theorem tsum_abs_liuSelbergCorrection_prime_pow
    {N p : ℕ} (hNeven : Even N) (hp : p.Prime) :
    (∑' e : ℕ, |liuSelbergCorrection N (p ^ e)|) =
      if p ∣ N then
        1 + (p : ℝ)⁻¹
      else
        1 + 3 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  by_cases hpn : p ∣ N
  · rw [if_pos hpn, tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ, liuSelbergCorrection_one,
        liuSelbergCorrection_prime_of_dvd hp hpn, abs_inv]
    · intro e he
      have he2 : 2 ≤ e := Nat.le_of_not_gt (by simpa using he)
      rw [liuSelbergCorrection_prime_pow_eq_zero_of_dvd hp hpn he2]
      simp
  · rw [if_neg hpn, tsum_eq_sum (s := Finset.range 3)]
    · have hp2 : 2 < p := by
        have hpne : p ≠ 2 := by
          intro h
          apply hpn
          rw [h]
          exact hNeven.two_dvd
        have := hp.two_le
        omega
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hpR2 : (0 : ℝ) < (p : ℝ) - 2 := by
        have : (2 : ℝ) < p := by exact_mod_cast hp2
        linarith
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        pow_zero, pow_one, liuSelbergCorrection_one, abs_one,
        liuSelbergCorrection_prime_of_not_dvd hNeven hp hpn,
        liuSelbergCorrection_prime_sq_of_not_dvd hp hpn]
      rw [abs_div, abs_div, abs_of_pos (mul_pos hpR hpR2)]
      norm_num
      field_simp [ne_of_gt hpR, ne_of_gt hpR2]
      ring
    · intro e he
      have he3 : 3 ≤ e := Nat.le_of_not_gt (by simpa using he)
      rw [liuSelbergCorrection_prime_pow_eq_zero_of_not_dvd hp hpn he3]
      simp

theorem tsum_liuSelbergCorrection_prime_pow_eq_localFactor_inv
    {N p : ℕ} (hNeven : Even N) (hp : p.Prime) :
    (∑' e : ℕ, liuSelbergCorrection N (p ^ e)) =
      (localFactor p N)⁻¹ := by
  by_cases hp2 : p = 2
  · subst p
    have h2N : 2 ∣ N := hNeven.two_dvd
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ,
        liuSelbergCorrection_prime_of_dvd Nat.prime_two h2N,
        localFactor_two hNeven]
      norm_num
    · intro e he
      have he2 : 2 ≤ e := Nat.le_of_not_gt (by simpa using he)
      rw [liuSelbergCorrection_prime_pow_eq_zero_of_dvd Nat.prime_two h2N he2]
  · have hpgt : 2 < p := by
      have := hp.two_le
      omega
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpR1 : (p : ℝ) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
    have hpR2 : (p : ℝ) - 2 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hp2)
    by_cases hpn : p ∣ N
    · rw [tsum_eq_sum (s := Finset.range 2)]
      · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          pow_zero, pow_one, liuSelbergCorrection_one,
          liuSelbergCorrection_prime_of_dvd hp hpn]
        rw [localFactor_of_dvd hp hpgt hpn]
        field_simp [hpR, hpR1]
        ring
      · intro e he
        have he2 : 2 ≤ e := Nat.le_of_not_gt (by simpa using he)
        rw [liuSelbergCorrection_prime_pow_eq_zero_of_dvd hp hpn he2]
    · rw [tsum_eq_sum (s := Finset.range 3)]
      · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          pow_zero, pow_one, liuSelbergCorrection_one,
          liuSelbergCorrection_prime_of_not_dvd hNeven hp hpn,
          liuSelbergCorrection_prime_sq_of_not_dvd hp hpn]
        rw [localFactor_of_not_dvd hp hpgt hpn]
        field_simp [hpR, hpR1, hpR2]
        ring
      · intro e he
        have he3 : 3 ≤ e := Nat.le_of_not_gt (by simpa using he)
        rw [liuSelbergCorrection_prime_pow_eq_zero_of_not_dvd hp hpn he3]

/-- The absolute local Euler total contains the unit term. -/
theorem liuSelbergAbsPrimeDeviation_nonneg_core
    {N : ℕ} (hNeven : Even N) (p : Nat.Primes) :
    0 ≤ liuSelbergAbsPrimeDeviation N p := by
  rw [liuSelbergAbsPrimeDeviation,
    tsum_abs_liuSelbergCorrection_prime_pow hNeven p.2]
  by_cases hpdvd : (p : ℕ) ∣ N
  · simp [hpdvd]
  · rw [if_neg hpdvd]
    have hp2 : 2 < (p : ℕ) := by
      have hpne : (p : ℕ) ≠ 2 := by
        intro heq
        apply hpdvd
        rw [heq]
        exact hNeven.two_dvd
      have := p.2.two_le
      omega
    have hpR : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    have hpR2 : (0 : ℝ) < ((p : ℕ) : ℝ) - 2 := by
      have : (2 : ℝ) < (p : ℕ) := by exact_mod_cast hp2
      linarith
    have hq : 0 ≤ 3 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2)) := by
      positivity
    linarith

theorem summable_liuSelbergAbsPrimeDeviation
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    Summable (liuSelbergAbsPrimeDeviation N) := by
  classical
  let d : Nat.Primes → ℝ :=
    fun p => if (p : ℕ) ∣ N then ((p : ℕ) : ℝ)⁻¹ else 0
  let b : Nat.Primes → ℝ :=
    fun p => 12 / (((p : ℕ) : ℝ) - 1) ^ 2
  have hd : Summable d := by
    let dNat : ℕ → ℝ :=
      fun p => if p ∈ N.primeFactors then (p : ℝ)⁻¹ else 0
    have hdNat : Summable dNat := by
      apply summable_of_ne_finset_zero (s := N.primeFactors)
      intro p hp
      simp only [dNat, if_neg hp]
    have hdsub := hdNat.subtype Nat.Prime
    apply hdsub.congr
    intro p
    simp only [Function.comp_apply, dNat, d]
    by_cases hpd : (p : ℕ) ∣ N
    · have hm : (p : ℕ) ∈ N.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨p.2, hpd, hN.ne'⟩
      simp [hm, hpd]
    · have hm : (p : ℕ) ∉ N.primeFactors := by
        simp [Nat.mem_primeFactors, hpd]
      simp [hm, hpd]
  have hb : Summable b := by
    apply ((summable_liuBaseDeviation_bound.mul_left 12).subtype Nat.Prime).congr
    intro p
    simp [b, Function.comp_apply, div_eq_mul_inv, mul_comm]
  apply Summable.of_nonneg_of_le
    (fun p => ?_) (fun p => ?_) (hd.add hb)
  · exact liuSelbergAbsPrimeDeviation_nonneg_core hNeven p
  · rw [liuSelbergAbsPrimeDeviation,
      tsum_abs_liuSelbergCorrection_prime_pow hNeven p.2]
    by_cases hpdvd : (p : ℕ) ∣ N
    · simp only [if_pos hpdvd, d, b]
      have hbnonneg :
          (0 : ℝ) ≤ 12 / (((p : ℕ) : ℝ) - 1) ^ 2 := by positivity
      linarith
    · simp only [if_neg hpdvd, d, b, zero_add]
      have hp2 : 2 < (p : ℕ) := by
        have hpne : (p : ℕ) ≠ 2 := by
          intro heq
          apply hpdvd
          rw [heq]
          exact hNeven.two_dvd
        have := p.2.two_le
        omega
      have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
      have hpR1 : (0 : ℝ) < ((p : ℕ) : ℝ) - 1 := by
        have : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < (p : ℕ))
        linarith
      have hpR2 : (0 : ℝ) < ((p : ℕ) : ℝ) - 2 := by
        have : (2 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp2
        linarith
      rw [show 1 + 3 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2)) - 1 =
        3 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 2)) by ring]
      rw [div_le_div_iff₀ (mul_pos hpR hpR2) (sq_pos_of_pos hpR1)]
      have hpR3 : (3 : ℝ) ≤ (p : ℕ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hp2)
      nlinarith [sq_nonneg (((p : ℕ) : ℝ) - 3)]

private theorem summable_norm_of_summable_prime_deviation
    (f : ℕ → ℝ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hfmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n)
    (hlocal : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖f (p ^ e)‖))
    (hdev : Summable (fun p : Nat.Primes => (∑' e : ℕ, ‖f (p ^ e)‖) - 1))
    (hdev_nonneg : ∀ p : Nat.Primes, 0 ≤ (∑' e : ℕ, ‖f (p ^ e)‖) - 1) :
    Summable (fun d : ℕ => ‖f d‖) := by
  classical
  have hmult :
      Multipliable (fun p : Nat.Primes => ∑' e : ℕ, ‖f ((p : ℕ) ^ e)‖) := by
    simpa only [add_sub_cancel] using
      Real.multipliable_one_add_of_summable hdev
  refine summable_of_sum_range_le
    (c := ∏' p : Nat.Primes, ∑' e : ℕ, ‖f ((p : ℕ) ^ e)‖)
    (fun _ => norm_nonneg _) fun z => ?_
  have hnorm1 : ‖f 1‖ = 1 := by simp [hf1]
  have hnorm_mul : ∀ {m n : ℕ}, m.Coprime n →
      ‖f (m * n)‖ = ‖f m‖ * ‖f n‖ := by
    intro m n hmn
    rw [hfmul hmn, norm_mul]
  have hsmooth :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := fun n => ‖f n‖) hnorm1 hnorm_mul (by
        intro p hp
        simpa only [norm_norm] using hlocal hp) z
  have hsind :
      Summable (z.smoothNumbers.indicator fun n => ‖f n‖) := by
    apply summable_subtype_iff_indicator.mp
    change Summable (fun n : z.smoothNumbers => ‖f (n : ℕ)‖)
    simpa only [norm_norm] using hsmooth.1
  calc
    ∑ n ∈ Finset.range z, ‖f n‖ =
        ∑ n ∈ Finset.range z,
          z.smoothNumbers.indicator (fun n => ‖f n‖) n := by
            apply sum_congr rfl
            intro n hn
            by_cases hn0 : n = 0
            · subst n
              simp [Set.indicator, hf0]
            · rw [Set.indicator_of_mem
                (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0)
                  (Finset.mem_range.mp hn))]
    _ ≤ ∑' n : ℕ, z.smoothNumbers.indicator (fun n => ‖f n‖) n :=
      hsind.sum_le_tsum _ (fun n _ => by
        by_cases hn : n ∈ z.smoothNumbers <;> simp [Set.indicator, hn])
    _ = ∑' n : z.smoothNumbers, ‖f n‖ := (_root_.tsum_subtype _ _).symm
    _ = ∏ p ∈ z.primesBelow, ∑' e : ℕ, ‖f (p ^ e)‖ := by
      simpa only using hsmooth.2.tsum_eq
    _ ≤ ∏' p : Nat.Primes, ∑' e : ℕ, ‖f ((p : ℕ) ^ e)‖ := by
      let e : z.primesBelow ↪ Nat.Primes :=
        ⟨fun p => ⟨p.1, Nat.prime_of_mem_primesBelow p.2⟩, by
          intro a b hab
          apply Subtype.ext
          exact congrArg (fun q : Nat.Primes => (q : ℕ)) hab⟩
      let S : Finset Nat.Primes := z.primesBelow.attach.map e
      have hprod :
          (∏ p ∈ z.primesBelow, ∑' k : ℕ, ‖f (p ^ k)‖) =
            ∏ p ∈ S, ∑' k : ℕ, ‖f ((p : ℕ) ^ k)‖ := by
        refine Finset.prod_bij (fun p hp => e ⟨p, hp⟩) ?_ ?_ ?_ ?_
        · intro p hp
          simp [S]
        · intro a ha b hb hab
          exact congrArg (fun q : Nat.Primes => (q : ℕ)) hab
        · intro p hp
          dsimp only [S] at hp
          obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
          exact ⟨q.1, q.2, rfl⟩
        · intro p hp
          rfl
      rw [hprod]
      exact ge_of_tendsto hmult.hasProd (Filter.eventually_atTop.mpr
        ⟨S, fun T hST =>
          Finset.prod_le_prod_of_subset_of_one_le hST
            (fun p _ => by linarith [hdev_nonneg p])
            (fun p _ _ => by linarith [hdev_nonneg p])⟩)

theorem summable_norm_liuSelbergCorrection
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    Summable (fun d : ℕ => ‖liuSelbergCorrection N d‖) := by
  apply summable_norm_of_summable_prime_deviation (liuSelbergCorrection N)
    (by simp) (by simp)
    (fun {_ _} hmn => (liuSelbergCorrection_isMultiplicative N).map_mul_of_coprime hmn)
  · intro p hp
    simpa only [Real.norm_eq_abs] using
      summable_abs_liuSelbergCorrection_prime_pow N hp
  · simp only [Real.norm_eq_abs]
    exact summable_liuSelbergAbsPrimeDeviation hNeven hN
  · intro p
    simp only [Real.norm_eq_abs]
    exact liuSelbergAbsPrimeDeviation_nonneg_core hNeven p

theorem summable_abs_liuSelbergCorrection
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    Summable (fun d : ℕ => |liuSelbergCorrection N d|) := by
  simpa only [Real.norm_eq_abs] using
    summable_norm_liuSelbergCorrection hNeven hN

private theorem summable_abs_liuSelbergCorrection_mul_fourthRoot
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    Summable (fun d : ℕ =>
      |liuSelbergCorrection N d| * Real.sqrt (Real.sqrt d)) := by
  classical
  let f : ℕ → ℝ :=
    fun d => |liuSelbergCorrection N d| * Real.sqrt (Real.sqrt d)
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 1 := by simp [f, liuSelbergCorrection_one]
  have hfmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [f, (liuSelbergCorrection_isMultiplicative N).map_mul_of_coprime hmn,
      abs_mul, Nat.cast_mul]
    rw [Real.sqrt_mul (Nat.cast_nonneg m),
      Real.sqrt_mul (Real.sqrt_nonneg (m : ℝ))]
    ring
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun e : ℕ => ‖f (p ^ e)‖) := by
    intro p hp
    by_cases hpn : p ∣ N
    · apply summable_of_ne_finset_zero (s := Finset.range 2)
      intro e he
      have he2 : 2 ≤ e := Nat.le_of_not_gt (by simpa using he)
      simp only [f]
      rw [liuSelbergCorrection_prime_pow_eq_zero_of_dvd hp hpn he2]
      simp
    · apply summable_of_ne_finset_zero (s := Finset.range 3)
      intro e he
      have he3 : 3 ≤ e := Nat.le_of_not_gt (by simpa using he)
      simp only [f]
      rw [liuSelbergCorrection_prime_pow_eq_zero_of_not_dvd hp hpn he3]
      simp
  have hdev_eq (p : Nat.Primes) :
      (∑' e : ℕ, ‖f ((p : ℕ) ^ e)‖) - 1 =
        if (p : ℕ) ∣ N then ‖f p‖ else ‖f p‖ + ‖f ((p : ℕ) ^ 2)‖ := by
    by_cases hpn : (p : ℕ) ∣ N
    · rw [if_pos hpn, tsum_eq_sum (s := Finset.range 2)]
      · simp [Finset.sum_range_succ, hf1]
      · intro e he
        have he2 : 2 ≤ e := Nat.le_of_not_gt (by simpa using he)
        simp only [f]
        rw [liuSelbergCorrection_prime_pow_eq_zero_of_dvd p.2 hpn he2]
        simp
    · rw [if_neg hpn, tsum_eq_sum (s := Finset.range 3)]
      · simp [Finset.sum_range_succ, hf1]
        ring
      · intro e he
        have he3 : 3 ≤ e := Nat.le_of_not_gt (by simpa using he)
        simp only [f]
        rw [liuSelbergCorrection_prime_pow_eq_zero_of_not_dvd p.2 hpn he3]
        simp
  let a : Nat.Primes → ℝ :=
    fun p => if (p : ℕ) ∣ N then ‖f p‖ else 0
  let b : Nat.Primes → ℝ :=
    fun p => 9 * (((p : ℕ) : ℝ) * Real.sqrt (p : ℕ))⁻¹
  have ha : Summable a := by
    let aNat : ℕ → ℝ :=
      fun p => if p ∈ N.primeFactors then ‖f p‖ else 0
    have haNat : Summable aNat := by
      apply summable_of_ne_finset_zero (s := N.primeFactors)
      intro p hp
      simp only [aNat, if_neg hp]
    apply (haNat.subtype Nat.Prime).congr
    intro p
    simp only [Function.comp_apply, aNat, a]
    by_cases hpd : (p : ℕ) ∣ N
    · have hm : (p : ℕ) ∈ N.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨p.2, hpd, hN.ne'⟩
      simp [hm, hpd]
    · have hm : (p : ℕ) ∉ N.primeFactors := by
        simp [Nat.mem_primeFactors, hpd]
      simp [hm, hpd]
  have hb : Summable b := by
    have hs :
        Summable (fun n : ℕ => (((n : ℝ) ^ (3 / 2 : ℝ))⁻¹)) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    apply ((hs.mul_left 9).subtype Nat.Prime).congr
    intro p
    have hpR : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    simp only [Function.comp_apply, b, Real.sqrt_eq_rpow]
    congr 2
    calc
      (p : ℝ) ^ (3 / 2 : ℝ) = (p : ℝ) ^ (1 + 1 / 2 : ℝ) := by norm_num
      _ = (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_add hpR 1 (1 / 2)
      _ = (p : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
  have hdev_nonneg (p : Nat.Primes) :
      0 ≤ (∑' e : ℕ, ‖f ((p : ℕ) ^ e)‖) - 1 := by
    rw [hdev_eq]
    split_ifs <;> positivity
  have hdev_le (p : Nat.Primes) :
      (∑' e : ℕ, ‖f ((p : ℕ) ^ e)‖) - 1 ≤ a p + b p := by
    rw [hdev_eq]
    by_cases hpd : (p : ℕ) ∣ N
    · simp [a, b, hpd]
      positivity
    · simp only [a, hpd, if_false, zero_add]
      have hp2 : 2 < (p : ℕ) := by
        have hpne : (p : ℕ) ≠ 2 := by
          intro heq
          have : (p : ℕ) ∣ N := by
            rw [heq]
            exact hNeven.two_dvd
          exact hpd this
        exact lt_of_le_of_ne p.2.two_le hpne.symm
      let P : ℝ := (p : ℕ)
      let s : ℝ := Real.sqrt P
      let r : ℝ := Real.sqrt s
      have hpR : 0 < P := by
        dsimp only [P]
        exact_mod_cast p.2.pos
      have hpR2 : 0 < P - 2 := by
        dsimp only [P]
        exact sub_pos.mpr (by exact_mod_cast hp2)
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (by
        dsimp only [P]
        exact_mod_cast p.2.one_lt.le)
      have hs_sq : s ^ 2 = P := Real.sq_sqrt hpR.le
      have hr0 : 0 ≤ r := Real.sqrt_nonneg _
      have hr_sq : r ^ 2 = s := Real.sq_sqrt hs0
      have hrle : r ≤ s := by nlinarith [sq_nonneg (s - r)]
      have hden : 0 < P * (P - 2) := mul_pos hpR hpR2
      have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs1
      have hfp : ‖f (p : ℕ)‖ = 2 / (P * (P - 2)) * r := by
        simp only [f, liuSelbergCorrection_prime_of_not_dvd hNeven p.2 hpd,
          Real.norm_eq_abs, abs_mul, abs_abs, abs_div]
        norm_num
        rw [abs_of_pos hpR2, abs_of_nonneg hr0]
      have hfp2 : ‖f ((p : ℕ) ^ 2)‖ = 1 / (P * (P - 2)) * s := by
        simp only [f, liuSelbergCorrection_prime_sq_of_not_dvd p.2 hpd,
          Real.norm_eq_abs, abs_mul, abs_abs, abs_div]
        norm_num
        rw [abs_of_pos hpR2, abs_of_nonneg hs0]
      rw [hfp, hfp2]
      change 2 / (P * (P - 2)) * r + 1 / (P * (P - 2)) * s ≤
        9 * (P * s)⁻¹
      rw [show 2 / (P * (P - 2)) * r + 1 / (P * (P - 2)) * s =
        (2 * r + s) / (P * (P - 2)) by field_simp]
      rw [show 9 * (P * s)⁻¹ = 9 / (P * s) by simp [div_eq_mul_inv]]
      rw [div_le_div_iff₀ hden (mul_pos hpR hspos)]
      have hnum : 2 * r + s ≤ 3 * s := by linarith
      have hmul := mul_le_mul_of_nonneg_right hnum (mul_nonneg hpR.le hs0)
      have hp3 : (3 : ℝ) ≤ P := by
        dsimp only [P]
        exact_mod_cast (Nat.succ_le_iff.mpr hp2)
      nlinarith [sq_nonneg P]
  have hdev : Summable
      (fun p : Nat.Primes => (∑' e : ℕ, ‖f ((p : ℕ) ^ e)‖) - 1) :=
    Summable.of_nonneg_of_le hdev_nonneg hdev_le (ha.add hb)
  have hf := summable_norm_of_summable_prime_deviation
    f hf0 hf1 hfmul hlocal hdev hdev_nonneg
  simpa only [f, Real.norm_eq_abs, abs_mul, abs_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using hf

theorem summable_abs_liuSelbergCorrection_mul_log
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    Summable (fun d : ℕ => |liuSelbergCorrection N d| * Real.log (2 * d)) := by
  have hroot (d : ℕ) :
      Real.sqrt (Real.sqrt d) = (d : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (Nat.cast_nonneg d)]
    norm_num
  have hmajorant :
      Summable (fun d : ℕ =>
        Real.log 2 * |liuSelbergCorrection N d| +
          4 * (|liuSelbergCorrection N d| * Real.sqrt (Real.sqrt d))) :=
    ((summable_abs_liuSelbergCorrection hNeven hN).mul_left (Real.log 2)).add
      ((summable_abs_liuSelbergCorrection_mul_fourthRoot hNeven hN).mul_left 4)
  apply Summable.of_nonneg_of_le
    (fun d => mul_nonneg (abs_nonneg _) (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        Real.log_natCast_nonneg (2 * d)))
    (fun d => ?_) hmajorant
  by_cases hd : d = 0
  · subst d
    simp
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hlog :
      Real.log (d : ℝ) ≤ 4 * Real.sqrt (Real.sqrt d) := by
    have h := Real.log_natCast_le_rpow_div d (by norm_num : (0 : ℝ) < 1 / 4)
    rw [← hroot] at h
    simpa [div_eq_mul_inv, mul_comm] using h
  rw [Real.log_mul (by norm_num) hdR]
  have := mul_le_mul_of_nonneg_left hlog (abs_nonneg (liuSelbergCorrection N d))
  nlinarith

theorem liuSelbergCorrection_finiteEulerProduct
    {N z : ℕ} (hNeven : Even N) (hz : 2 ≤ z) :
    (∏ p ∈ (z + 1).primesBelow,
        ∑' e : ℕ, liuSelbergCorrection N (p ^ e)) =
      1 / (2 * liuSingularSeriesTruncated N z) := by
  rw [show (z + 1).primesBelow =
      (Finset.range (z + 1)).filter Nat.Prime by rfl]
  calc
    ∏ p ∈ (Finset.range (z + 1)).filter Nat.Prime,
        ∑' e : ℕ, liuSelbergCorrection N (p ^ e) =
      ∏ p ∈ (Finset.range (z + 1)).filter Nat.Prime,
        (localFactor p N)⁻¹ := by
          apply prod_congr rfl
          intro p hp
          exact tsum_liuSelbergCorrection_prime_pow_eq_localFactor_inv
            hNeven (Finset.mem_filter.mp hp).2
    _ = (singularSeriesTruncated N z)⁻¹ := by
      rw [Finset.prod_inv_distrib]
      rfl
    _ = 1 / (2 * liuSingularSeriesTruncated N z) := by
      rw [singularSeriesTruncated_eq_two_mul_liuSingularSeriesTruncated
        N z hNeven hz]
      simp [div_eq_mul_inv]

theorem tsum_liuSelbergCorrection
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    (∑' d : ℕ, liuSelbergCorrection N d) =
      1 / (2 * liuSingularSeries N) := by
  have hs := summable_norm_liuSelbergCorrection hNeven hN
  have heuler :=
    (liuSelbergCorrection_isMultiplicative N).eulerProduct hs
  have heuler' :
      Filter.Tendsto
        (fun z : ℕ => ∏ p ∈ (z + 1).primesBelow,
          ∑' e : ℕ, liuSelbergCorrection N (p ^ e))
        Filter.atTop (nhds (∑' d : ℕ, liuSelbergCorrection N d)) :=
    heuler.comp (Filter.tendsto_add_atTop_nat 1)
  have hsing :
      Filter.Tendsto (fun z : ℕ => 1 / (2 * liuSingularSeriesTruncated N z))
        Filter.atTop (nhds (1 / (2 * liuSingularSeries N))) := by
    have hmul :
        Filter.Tendsto
          (fun z : ℕ => (2 : ℝ) * liuSingularSeriesTruncated N z)
          Filter.atTop (nhds ((2 : ℝ) * liuSingularSeries N)) :=
      tendsto_const_nhds.mul (tendsto_liuSingularSeriesTruncated N hN)
    simpa only [one_div] using hmul.inv₀
      (mul_ne_zero (by norm_num) (ne_of_gt (liuSingularSeries_pos N)))
  apply tendsto_nhds_unique heuler'
  apply hsing.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with z hz
  exact (liuSelbergCorrection_finiteEulerProduct hNeven hz).symm

theorem tendsto_liuSelbergCorrection_partialSums
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    Filter.Tendsto
      (fun x : ℕ => ∑ d ∈ Finset.Icc 1 x, liuSelbergCorrection N d)
      Filter.atTop (nhds (1 / (2 * liuSingularSeries N))) := by
  have hs := (summable_norm_liuSelbergCorrection hNeven hN).of_norm
  have ht := hs.hasSum.tendsto_sum_nat
  have ht' := ht.comp (Filter.tendsto_add_atTop_nat 1)
  rw [tsum_liuSelbergCorrection hNeven hN] at ht'
  apply ht'.congr'
  filter_upwards [] with x
  rw [show Finset.Icc 1 x = (Finset.range (x + 1)).erase 0 by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    omega]
  simp

end MathlibNt.SieveTheory.LiuWeight
