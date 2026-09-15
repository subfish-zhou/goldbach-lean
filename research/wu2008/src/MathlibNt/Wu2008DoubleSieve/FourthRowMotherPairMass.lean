import MathlibNt.Wu2008DoubleSieve.FourthRowMotherSourceBands

/-! # Exact two-prime raw carrier mass, retaining both selected labels -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem fourthRowMother_pair_mass (N d : ℕ) (a u v w : ℝ) :
    fourthRowMotherPair N d (d * N) a u v w =
      ∑ ell ∈ sieveCarrier N d (d * N) a,
        ((((divisorsIn (primeWindow (d * N) a u) ((N - ell) / d)) ×ˢ
          (divisorsIn (primeWindow (d * N) v w) ((N - ell) / d))).filter
            (fun pq => pq.1 < pq.2)).card : ℝ) := by
  have hs (p : ℕ) (hp : p ∈ primeWindow (d * N) a u)
      (q : ℕ) (hq : q ∈ primeWindow (d * N) v w) :
      (if p < q then (sourceSieveCount N (d * p * q) (d * N) a : ℝ) else 0) =
        ∑ ell ∈ sieveCarrier N d (d * N) a,
          if p ∣ (N - ell) / d ∧ q ∣ (N - ell) / d ∧ p < q then (1 : ℝ) else 0 := by
    by_cases hpq : p < q
    · have hprod (n : ℕ) : p * q ∣ n ↔ p ∣ n ∧ q ∣ n := by
        constructor
        · intro h
          exact ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩
        · rintro ⟨hp', hq'⟩
          exact ((Nat.coprime_primes (mem_primeWindow.mp hp).1 (mem_primeWindow.mp hq).1).mpr
            (ne_of_lt hpq)).mul_dvd_of_dvd_of_dvd hp' hq'
      simp only [hpq, if_true, and_true, sourceSieveCount, Int.cast_natCast, mul_assoc]
      simp only [← fourthRowMother_fixed_carrier N d (p * q) (d * N) a (dvd_mul_right d N),
        ← sum_boole, hprod]
    · simp only [hpq, if_false, and_false, sum_const_zero]
  unfold fourthRowMotherPair
  calc
    _ = ∑ q ∈ primeWindow (d * N) v w, ∑ p ∈ primeWindow (d * N) a u,
        ∑ ell ∈ sieveCarrier N d (d * N) a,
          if p ∣ (N - ell) / d ∧ q ∣ (N - ell) / d ∧ p < q then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro q hq
      exact sum_congr rfl fun p hp => hs p hp q hq
    _ = ∑ q ∈ primeWindow (d * N) v w, ∑ ell ∈ sieveCarrier N d (d * N) a,
        ∑ p ∈ primeWindow (d * N) a u,
          if p ∣ (N - ell) / d ∧ q ∣ (N - ell) / d ∧ p < q then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro q _
      rw [sum_comm]
    _ = ∑ ell ∈ sieveCarrier N d (d * N) a, ∑ q ∈ primeWindow (d * N) v w,
        ∑ p ∈ primeWindow (d * N) a u,
          if p ∣ (N - ell) / d ∧ q ∣ (N - ell) / d ∧ p < q then (1 : ℝ) else 0 := by
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro ell _
      rw [sum_comm]
      simp only [← sum_boole, sum_product, divisorsIn, sum_filter]
      apply sum_congr rfl
      intro p _
      by_cases hp : p ∣ (N - ell) / d
      · simp only [hp, true_and, if_true]
        apply sum_congr rfl
        intro q _
        by_cases hq : q ∣ (N - ell) / d <;> simp [hq]
      · simp only [hp, false_and, if_false, sum_const_zero]

theorem fourthRowMother_gamma5_mass (N d : ℕ) {a b c f : ℝ}
    (hbc : b ≤ c) (hcf : c ≤ f) :
    fourthRowMotherPair N d (d * N) a c a c =
      ∑ ell ∈ sieveCarrier N d (d * N) a,
        ((fourthRowMotherLowPairs
          (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d))
          (fourthRowMotherColour b c)).card : ℝ) := by
  rw [fourthRowMother_pair_mass]
  simp only [fourthRowMotherLowPairs, fourthRowMother_band_low _ _ hbc hcf]

theorem fourthRowMother_gamma6_mass (N d : ℕ) {a b c f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcf : c ≤ f) :
    fourthRowMotherPair N d (d * N) a b c f =
      ∑ ell ∈ sieveCarrier N d (d * N) a,
        ((fourthRowMotherCrossPairs
          (divisorsIn (primeWindow (d * N) a f) ((N - ell) / d))
          (fourthRowMotherColour b c)).card : ℝ) := by
  rw [fourthRowMother_pair_mass]
  apply sum_congr rfl
  intro ell _
  have he :
      (((divisorsIn (primeWindow (d * N) a b) ((N - ell) / d)) ×ˢ
        (divisorsIn (primeWindow (d * N) c f) ((N - ell) / d))).filter
          (fun pq => pq.1 < pq.2)) =
      (divisorsIn (primeWindow (d * N) a b) ((N - ell) / d)) ×ˢ
        (divisorsIn (primeWindow (d * N) c f) ((N - ell) / d)) := by
    apply filter_eq_self.mpr
    rintro ⟨p, q⟩ hpq
    obtain ⟨hp, hq⟩ := mem_product.mp hpq
    have hp' := (mem_primeWindow.mp (mem_filter.mp hp).1).2.2.2
    have hq' := (mem_primeWindow.mp (mem_filter.mp hq).1).2.2.1
    have hh : (p : ℝ) < q := hp'.trans_le (hbc.trans hq')
    exact_mod_cast hh
  rw [he]
  simp only [fourthRowMotherCrossPairs, fourthRowMother_band_zero _ _ (hbc.trans hcf),
    fourthRowMother_band_two _ _ hab hbc]

end Wu2008DoubleSieve
