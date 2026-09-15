import MathlibNt.Wu2008DoubleSieve.FourthRowMotherFourBridge

/-! # Exact raw fixed-cutoff and prefix pair/triple carrier identities -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem fourthRowMother_fixed_carrier (N d k M : ℕ) (a : ℝ) (hdM : d ∣ M) :
    (sieveCarrier N d M a).filter (fun ell => k ∣ (N - ell) / d) =
      sourceSieveCarrier N (d * k) M a := by
  ext ell
  simp only [sieveCarrier, sourceSieveCarrier, mem_filter]
  constructor
  · rintro ⟨⟨hr, hp, hd, hs⟩, hk⟩
    exact ⟨hr, hp, (Nat.dvd_div_iff_mul_dvd hd).mp hk,
      (sifted_quotient_iff hd (fun _ _ hq _ => hq.of_dvd_right hdM)).mp hs⟩
  · rintro ⟨hr, hp, hdk, hs⟩
    have hd : d ∣ N - ell := (dvd_mul_right d k).trans hdk
    exact ⟨⟨hr, hp, hd,
      (sifted_quotient_iff hd (fun _ _ hq _ => hq.of_dvd_right hdM)).mpr hs⟩,
      (Nat.dvd_div_iff_mul_dvd hd).mpr hdk⟩

theorem fourthRowMother_raise_cutoff {M n p : ℕ} {a f : ℝ}
    (hap : a ≤ (p : ℝ)) (hpf : (p : ℝ) < f) :
    Sifted M n p ↔ Sifted M n a ∧
      ∀ q ∈ divisorsIn (primeWindow M a f) n, p ≤ q := by
  constructor
  · intro hs
    refine ⟨fun q hq hqM hqa => hs q hq hqM (hqa.trans_le hap), ?_⟩
    intro q hq
    obtain ⟨hq, hqn⟩ := mem_filter.mp hq
    obtain ⟨hqp, hqM, _, _⟩ := mem_primeWindow.mp hq
    by_contra h
    exact hs q hqp hqM (by exact_mod_cast (show q < p by omega)) hqn
  · rintro ⟨hs, hm⟩ q hq hqM hqp hqn
    by_cases hqa : (q : ℝ) < a
    · exact hs q hq hqM hqa hqn
    · have hm' := hm q (mem_filter.mpr
        ⟨mem_primeWindow.mpr ⟨hq, hqM, le_of_not_gt hqa, hqp.trans hpf⟩, hqn⟩)
      have hqp' : q < p := by exact_mod_cast hqp
      omega

theorem fourthRowMother_pair_carrier (N d : ℕ) {a f : ℝ} {p q : ℕ}
    (hp : p ∈ primeWindow (d * N) a f) (hq : q ∈ primeWindow (d * N) a f)
    (hpq : p < q) :
    (sieveCarrier N d (d * N) a).filter
      (fun ell => [p, q] ∈ fourthRowMotherPrefixes
        (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d)) 2) =
      sourceSieveCarrier N (d * (p * q)) (d * N) p := by
  obtain ⟨hpp, _, hap, hpf⟩ := mem_primeWindow.mp hp
  obtain ⟨hqp, _, _, _⟩ := mem_primeWindow.mp hq
  have hprod (n : ℕ) : p * q ∣ n ↔ p ∣ n ∧ q ∣ n := by
    constructor
    · intro h
      exact ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩
    · rintro ⟨hpn, hqn⟩
      exact ((Nat.coprime_primes hpp hqp).mpr (ne_of_lt hpq)).mul_dvd_of_dvd_of_dvd hpn hqn
  rw [← fourthRowMother_fixed_carrier N d (p * q) (d * N) p (dvd_mul_right d N)]
  ext ell
  simp only [sieveCarrier, mem_filter, fourthRowMother_mem_pair, divisorsIn, mem_filter,
    hprod, fourthRowMother_raise_cutoff hap hpf]
  constructor
  · rintro ⟨⟨hell, hpell, hd, hs⟩, ⟨_, hpn⟩, ⟨_, hqn⟩, _, hm⟩
    exact ⟨⟨hell, hpell, hd, hs, hm⟩, hpn, hqn⟩
  · rintro ⟨⟨hell, hpell, hd, hs, hm⟩, hpn, hqn⟩
    exact ⟨⟨hell, hpell, hd, hs⟩, ⟨hp, hpn⟩, ⟨hq, hqn⟩, hpq, hm⟩

theorem fourthRowMother_triple_carrier (N d : ℕ) {a f : ℝ} {p q r : ℕ}
    (ht : (p, q, r) ∈ orderedTriples (primeWindow (d * N) a f)) :
    (sieveCarrier N d (d * N) a).filter
      (fun ell => [p, q, r] ∈ fourthRowMotherPrefixes
        (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d)) 3) =
      sourceSieveCarrier N (d * (p * q * r)) (d * p * N) q := by
  have he :
      (sieveCarrier N d (d * N) a).filter
        (fun ell => [p, q, r] ∈ fourthRowMotherPrefixes
          (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d)) 3) =
      (sieveCarrier N d (d * N) a).filter
        (fun ell => tripleSurvives (primeWindow (d * N) a f) ((N - ell) / d) (p, q, r)) := by
    ext ell
    simp only [mem_filter, fourthRowMother_mem_triple, firstTwoTriples_divisorsIn, ht, true_and]
  rw [he, tripleCarrier_eq N d (d * N) ht]
  have ht' := ht
  simp only [orderedTriples, mem_filter, mem_product] at ht'
  obtain ⟨⟨_, hq, hr⟩, _, hqr⟩ := ht'
  have hqp := (mem_primeWindow.mp hq).1
  have hrp := (mem_primeWindow.mp hr).1
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (source_strict_triple_carrier (N := N) (a := d * p) hqp hrp hqr.le).symm

end Wu2008DoubleSieve
