import MathlibNt.Wu2008DoubleSieve.Gamma16Profiles

/-! # Positive quotient reconstruction and the genuine good-label conditions -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

def gamma16Quotient (N d : ℕ) (p : Gamma16Tuple) (ell : ℕ) : ℕ :=
  (N - ell) / (d * gamma16Product p)

def gamma16SwitchProfile (N d : ℕ) (p : Gamma16Tuple) (ell : ℕ) : Gamma16Profile :=
  ⟨d, p 2, p 1, p 0, gamma16Quotient N d p ell⟩

theorem gamma16_quotient_equation {N d ell : ℕ} {p : Gamma16Tuple}
    (hell : ell < N) (hdiv : d * gamma16Product p ∣ N - ell) :
    0 < gamma16Quotient N d p ell ∧
      gamma16Cofactor (gamma16SwitchProfile N d p ell) * p 3 = N - ell ∧
      ell = N - gamma16Cofactor (gamma16SwitchProfile N d p ell) * p 3 ∧
      gamma16Cofactor (gamma16SwitchProfile N d p ell) * p 3 ≤ N := by
  have hd : d * (p 0 * p 1) * p 2 * p 3 ∣ N - ell := by
    simpa only [gamma16Product, mul_assoc] using hdiv
  simpa only [gamma16Quotient, gamma16Product, gamma16SwitchProfile, gamma16Cofactor,
    omega3Quotient, omega3Cofactor, mul_assoc] using omega3_quotient_equation hell hd

theorem gamma16_complement_div {N d ell : ℕ} {p : Gamma16Tuple}
    (hd : 0 < d) (hdiv : d * gamma16Product p ∣ N - ell) :
    (N - ell) / d = gamma16Product p * gamma16Quotient N d p ell := by
  have hdiv' : d * (p 0 * p 1) * p 2 * p 3 ∣ N - ell := by
    simpa only [gamma16Product, mul_assoc] using hdiv
  simpa only [gamma16Product, gamma16Quotient, omega3Quotient, mul_assoc] using
    omega3_complement_div hd hdiv'

theorem gamma16_strengthened_of_prefix {N d ell : ℕ} {δ : ℝ} {p : Gamma16Tuple}
    (hd : 0 < d) (hp : p ∈ gamma16Tuples N δ d)
    (hell : ell ∈ gamma16PrefixCarrier N d p)
    (hgoodd : ¬Omega3BadD N d ell) (hgoodN : ¬ell ∣ N) :
    Gamma16Strengthened N d (p 0) (p 1) (p 2) (gamma16Quotient N d p ell) := by
  obtain ⟨h, _⟩ := mem_gamma16Tuples.mp hp
  obtain ⟨hellN, hprime, hdiv, hsieve⟩ := mem_filter.mp hell
  have hellle : ell ≤ N := Nat.le_of_lt_succ (mem_range.mp hellN)
  let n := gamma16Quotient N d p ell
  have hcomp : d.Coprime (gamma16Product p * n) := by
    have hg : d.Coprime ((N - ell) / d) := by simpa only [Omega3BadD, not_not] using hgoodd
    simpa only [gamma16_complement_div hd hdiv] using hg
  have hprefix : (p 0 * p 1 * p 2).Coprime d :=
    (hcomp.of_dvd_right ⟨p 3 * n, by simp only [gamma16Product]; ring⟩).symm
  have hnd : n.Coprime d :=
    (hcomp.of_dvd_right (dvd_mul_left n (gamma16Product p))).symm
  have hnN : n.Coprime N := by
    have hdiv' : d * (p 0 * p 1) * p 2 * p 3 ∣ N - ell := by
      simpa only [gamma16Product, mul_assoc] using hdiv
    simpa only [n, gamma16Quotient, gamma16Product, omega3Quotient, mul_assoc] using
      omega3_quotient_coprime_of_output hprime hellle hgoodN hdiv'
  refine ⟨hprefix.mul_right (((h 0).2.1.mul_left (h 1).2.1).mul_left (h 2).2.1),
    hnd.mul_right hnN, ?_⟩
  intro q hq hsmall hq0 hq1 hqn
  have hqd := hnd.of_dvd_left hqn
  have hqN := hnN.of_dvd_left hqn
  have hc0 := (Nat.coprime_primes hq (h 0).1).mpr hq0
  have hc1 := (Nat.coprime_primes hq (h 1).1).mpr hq1
  apply hsieve q hq (((hqd.mul_right hc0).mul_right hc1).mul_right hqN) hsmall
  exact hqn.trans ⟨d * gamma16Product p,
    (Nat.mul_div_cancel' hdiv).symm.trans (mul_comm _ _)⟩

theorem gamma16_raw_is_bad {N d ell : ℕ} {δ : ℝ} {p : Gamma16Tuple}
    (hd : 0 < d) (hp : p ∈ gamma16Tuples N δ d)
    (hell : ell ∈ gamma16RawCarrier N d p) : Omega3BadD N d ell := by
  have hf : p 0 ∣ d ∧ p 1 ∣ d := by
    by_contra hn
    rw [gamma16_raw_carrier_ite hp, if_neg hn] at hell
    exact notMem_empty _ hell
  have hdiv := (mem_filter.mp hell).2.2.1
  have hprime := (mem_gamma16Tuples.mp hp).1 0 |>.1
  intro hcop
  have hpcomp : p 0 ∣ (N - ell) / d := by
    rw [gamma16_complement_div hd hdiv]
    exact ⟨p 1 * p 2 * p 3 * gamma16Quotient N d p ell, by
      simp only [gamma16Product]; ring⟩
  exact hprime.not_dvd_one (by
    simpa only [hcop.gcd_eq_one] using Nat.dvd_gcd hf.1 hpcomp)

theorem gamma16_switch_profile_mem {i N d ell : ℕ} {δ : ℝ} {W : Fin i → Finset ℕ}
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (hdW : d ∈ boxConvolutionSupport W)
    {p : Gamma16Tuple} (hp : p ∈ gamma16Tuples N δ d)
    (hell : ell ∈ gamma16PrefixCarrier N d p)
    (hgoodd : ¬Omega3BadD N d ell) (hgoodN : ¬ell ∣ N) :
    gamma16SwitchProfile N d p ell ∈ gamma16Profiles N δ W ∧
      p 3 ∈ gamma16StrictFibre N δ (gamma16SwitchProfile N d p ell) := by
  obtain ⟨h, h01, h12, h23, _⟩ := mem_gamma16Tuples.mp hp
  obtain ⟨hellN, hprime, hdiv, _⟩ := mem_filter.mp hell
  have hlt := omega3_prime_output_lt hN he hprime
    (Nat.le_of_lt_succ (mem_range.mp hellN))
  have hq := gamma16_quotient_equation hlt hdiv
  have hnN : gamma16Quotient N d p ell ≤ N :=
    (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  constructor
  · apply mem_gamma16Profiles.mpr
    exact ⟨hdW, mem_primeWindow.mpr (h 2),
      mem_primeWindow.mpr ⟨(h 1).1, (h 1).2.1, (h 1).2.2.1, by exact_mod_cast h12⟩,
      mem_primeWindow.mpr ⟨(h 0).1, (h 0).2.1, (h 0).2.2.1, by exact_mod_cast h01⟩,
      hnN, hq.1, (Nat.mul_le_mul_left _ h23.le).trans hq.2.2.2,
      gamma16_strengthened_of_prefix hd hp hell hgoodd hgoodN⟩
  · apply mem_filter.mpr
    exact ⟨mem_primeWindow.mpr
      ⟨(h 3).1, (h 3).2.1, by exact_mod_cast h23.le, (h 3).2.2.2⟩, h23, hq.2.2.2⟩

end Wu2008DoubleSieve
