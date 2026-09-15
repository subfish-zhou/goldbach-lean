import MathlibNt.Wu2008DoubleSieve.FourthRowMotherCarriers
import MathlibNt.Wu2008DoubleSieve.Omega3FiniteError
import MathlibNt.Wu2008DoubleSieve.Omega3ErrorBudget

/-! # Exact original-window correction and its narrow single-output floor bound -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def fourthRowMotherBadPrime (N d : ℕ) (a u : ℝ) : ℝ :=
  ∑ p ∈ (primeWindow N a u).filter (fun p => p ∣ d),
    (sourceSieveCount N (d * p) (d * N) a : ℝ)

theorem fourthRowMother_negative_split (N d : ℕ) (a u : ℝ) :
    fourthRowMotherSingle N d N a u =
      fourthRowMotherSingle N d (d * N) a u + fourthRowMotherBadPrime N d a u := by
  have h := primeWindow_modulus_sum_difference N d a u
    (fun p => (sourceSieveCount N (d * p) (d * N) a : ℝ))
  change fourthRowMotherSingle N d N a u -
    fourthRowMotherSingle N d (d * N) a u = fourthRowMotherBadPrime N d a u at h
  linarith

theorem fourthRowMother_bad_prime_nonneg (N d : ℕ) (a u : ℝ) :
    0 ≤ fourthRowMotherBadPrime N d a u :=
  sum_nonneg fun _ _ => by simp only [sourceSieveCount, Int.cast_natCast]; positivity

theorem fourthRowMother_bad_prime_mono (N d : ℕ) (a : ℝ) {u v : ℝ} (huv : u ≤ v) :
    fourthRowMotherBadPrime N d a u ≤ fourthRowMotherBadPrime N d a v := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp, hpd⟩ := mem_filter.mp hp
    obtain ⟨hpp, hpN, hap, hpu⟩ := mem_primeWindow.mp hp
    exact mem_filter.mpr ⟨mem_primeWindow.mpr ⟨hpp, hpN, hap, hpu.trans_le huv⟩, hpd⟩
  · intro p _ _
    simp only [sourceSieveCount, Int.cast_natCast]
    positivity

theorem fourthRowMother_bad_prime_is_badD {N d p ell : ℕ} {a : ℝ}
    (hp : p.Prime) (hpd : p ∣ d)
    (hell : ell ∈ sourceSieveCarrier N (d * p) (d * N) a) :
    p ∣ d ∧ p ∣ (N - ell) / d ∧ ¬d.Coprime ((N - ell) / d) := by
  have hdiv := (mem_filter.mp hell).2.2.1
  have hd : d ∣ N - ell := (dvd_mul_right d p).trans hdiv
  have hpn := (Nat.dvd_div_iff_mul_dvd hd).mpr hdiv
  exact ⟨hpd, hpn, Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpd, hpn⟩⟩

theorem fourthRowMother_single_floor {N d p : ℕ} {a : ℝ}
    (hN : 4 ≤ N) (he : Even N) :
    (sourceSieveCarrier N (d * p) (d * N) a).card ≤ N / (d * p) := by
  calc
    _ ≤ ((range (N + 1)).filter fun m => m ≠ 0 ∧ d * p ∣ m).card := by
      apply card_le_card_of_injOn (fun ell => N - ell)
      · intro ell hell
        change N - ell ∈ _
        obtain ⟨hrange, hprime, hdiv, _⟩ := mem_filter.mp hell
        have hlt := omega3_prime_output_lt hN he hprime
          (Nat.le_of_lt_succ (mem_range.mp hrange))
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), by omega, hdiv⟩
      · intro ell hell ell' hell' h
        dsimp at h
        have hle := mem_range.mp (mem_filter.mp hell).1
        have hle' := mem_range.mp (mem_filter.mp hell').1
        omega
    _ = _ := Nat.card_multiples' N (d * p)

theorem fourthRowMother_bad_prime_floor {N d : ℕ} (a u : ℝ)
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) :
    fourthRowMotherBadPrime N d a u ≤
      ∑ p ∈ d.primeFactors, ((N / (d * p) : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ p ∈ (primeWindow N a u).filter (fun p => p ∣ d),
        ((N / (d * p) : ℕ) : ℝ) := by
      apply sum_le_sum
      intro p _
      simpa only [sourceSieveCount, Int.cast_natCast, Nat.cast_le] using
        fourthRowMother_single_floor (d := d) (p := p) (a := a) hN he
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hp, hpd⟩ := mem_filter.mp hp
        exact Nat.mem_primeFactors.mpr ⟨(mem_primeWindow.mp hp).1, hpd, Nat.ne_of_gt hd⟩
      · intro p _ _
        exact Nat.cast_nonneg _

theorem fourthRowMother_error_power {N d : ℕ} {a c f η : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (hdN : d ≤ N)
    (hcf : c ≤ f) (hη : 0 < η)
    (hlarge : ∀ p ∈ d.primeFactors, (N : ℝ) ^ η ≤ (p : ℝ)) :
    2 * fourthRowMotherBadPrime N d a f + fourthRowMotherBadPrime N d a c ≤
      (3 / η) * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η) := by
  have hm := fourthRowMother_bad_prime_mono N d a hcf
  have hf := (fourthRowMother_bad_prime_floor a f hN he hd).trans
    (omega3_bad_floor_sum_le (by omega) hd hdN hη hlarge)
  calc
    _ ≤ 3 * fourthRowMotherBadPrime N d a f := by linarith
    _ ≤ 3 * ((1 / η) * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η)) := by linarith
    _ = _ := by ring

end Wu2008DoubleSieve
