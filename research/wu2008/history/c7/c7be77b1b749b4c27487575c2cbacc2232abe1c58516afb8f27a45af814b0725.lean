import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedProfiles

/-! # The physical upper sieve on the fixed gated prime fibre -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple MathlibNt.SieveTheory.LinearSieve

noncomputable def fourthRowTripleGatedX {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) : ℝ :=
  ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) * (fourthRowTripleGatedFibre N δ c).card

noncomputable def fourthRowTripleGatedS {i : ℕ} (N : ℕ) (δ Z : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) : ℝ :=
  ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) *
    (((fourthRowTripleGatedFibre N δ c).filter
      (fun p => Sifted N (N - omega3CofactorValue c * p) Z)).card : ℝ)

noncomputable def fourthRowTripleGatedWeight {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (b : ℕ) : ℝ :=
  ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) *
    (((fourthRowTripleGatedFibre N δ c).filter
      (fun p => N - omega3CofactorValue c * p = b)).card : ℝ)

noncomputable def fourthRowTripleGatedAP (N : ℕ) (δ : ℝ) (c : Omega3CofactorIndex) (q : ℕ) : ℕ :=
  ((fourthRowTripleGatedFibre N δ c).filter (fun p => Nat.ModEq q (omega3CofactorValue c * p) N)).card

noncomputable def fourthRowTripleGatedResidual {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (q : ℕ) : ℝ :=
  ∑ c ∈ L.filter (fun c => (omega3CofactorValue c).Coprime q),
    (convolutionCoeff W c.1 : ℝ) *
      ((fourthRowTripleGatedAP N δ c q : ℝ) -
        (fourthRowTripleGatedFibre N δ c).card / (Nat.totient q : ℝ))

noncomputable def fourthRowTripleGatedMissing {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (q : ℕ) : ℝ :=
  ∑ c ∈ L.filter (fun c => ¬(omega3CofactorValue c).Coprime q),
    (convolutionCoeff W c.1 : ℝ) * (fourthRowTripleGatedFibre N δ c).card

noncomputable def fourthRowTripleGatedR1 {i : ℕ} (N D : ℕ) (δ Z : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z, (3 : ℝ) ^ q.primeFactors.card *
    |fourthRowTripleGatedResidual N δ W L q|

noncomputable def fourthRowTripleGatedR2 {i : ℕ} (N D : ℕ) (δ Z : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z, ((3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) *
    fourthRowTripleGatedMissing N δ W L q

noncomputable def fourthRowTripleGatedSieve {i : ℕ} (N : ℕ) (he : Even N) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) : BoundingSieve where
  support := range (N + 1)
  prodPrimes := ordinarySievePrimeProduct N Z
  prodPrimes_squarefree := ordinarySievePrimeProduct_squarefree _ _
  weights := fourthRowTripleGatedWeight N δ W L
  weights_nonneg := fun _ => sum_nonneg fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  totalMass := fourthRowTripleGatedX N δ W L
  nu := goldbachNu
  nu_mult := goldbachNu_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp hd => goldbachNu_lt_one_of_prime hp
    (ordinarySievePrimeProduct_prime_gt_two he Z hp hd)

theorem fourthRowTripleGated_AP_divisible (N : ℕ) (δ : ℝ) (c : Omega3CofactorIndex) (q : ℕ) :
    fourthRowTripleGatedAP N δ c q =
      ((fourthRowTripleGatedFibre N δ c).filter (fun p => q ∣ N - omega3CofactorValue c * p)).card := by
  unfold fourthRowTripleGatedAP
  congr 1
  apply filter_congr
  intro p hp
  exact Nat.modEq_iff_dvd' (mem_filter.mp (mem_filter.mp hp).1).2.2.2.2

theorem fourthRowTripleGated_AP_zero {N q : ℕ} {δ : ℝ} {c : Omega3CofactorIndex}
    (hq : q.Coprime N) (hc : ¬(omega3CofactorValue c).Coprime q) :
    fourthRowTripleGatedAP N δ c q = 0 := by
  have hh : fourthRowTripleGatedAP N δ c q ≤ omega3SieveAPCount N δ (5 / 2) c q :=
    card_le_card (filter_subset_filter _ (filter_subset _ _))
  rw [omega3SieveAPCount_eq_zero_of_not_coprime hq hc] at hh
  omega

theorem fourthRowTripleGated_AP_profile {N q : ℕ} {δ : ℝ} {c : Omega3CofactorIndex}
    (he : 0 < omega3CofactorValue c) (hH : 0 < wuLocalCutoff N δ c.1 (291 / 100)) :
    (fourthRowTripleGatedAP N δ c q : ℝ) -
      (fourthRowTripleGatedFibre N δ c).card / (Nat.totient q : ℝ) =
      omega3ProfileError N q (omega3CofactorValue c)
        (fourthRowTripleGatedLower N δ c) (fourthRowTripleGatedUpper N δ c) := by
  unfold fourthRowTripleGatedAP omega3ProfileError
  rw [fourthRowTripleGated_fibre_profile he hH]

theorem fourthRowTripleGated_output_test {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (f : ℕ → ℝ) :
    (∑ b ∈ range (N + 1), fourthRowTripleGatedWeight N δ W L b * f b) =
      ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) *
        ∑ p ∈ fourthRowTripleGatedFibre N δ c, f (N - omega3CofactorValue c * p) := by
  unfold fourthRowTripleGatedWeight
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  have hb : N - omega3CofactorValue c * p ∈ range (N + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
  rw [sum_eq_single (N - omega3CofactorValue c * p)]
  · simp
  · intro b _ hn
    simp [Ne.symm hn]
  · exact fun hn => (hn hb).elim

theorem fourthRowTripleGated_mass {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) :
    (∑ b ∈ range (N + 1), fourthRowTripleGatedWeight N δ W L b) =
      fourthRowTripleGatedX N δ W L := by
  simpa only [fourthRowTripleGatedX, mul_one, sum_const, nsmul_eq_mul] using
    fourthRowTripleGated_output_test N δ W L (fun _ => 1)

theorem fourthRowTripleGated_sifted {i : ℕ} (N : ℕ) (he : Even N) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) :
    (fourthRowTripleGatedSieve N he δ Z W L).siftedSum = fourthRowTripleGatedS N δ Z W L := by
  have h := fourthRowTripleGated_output_test N δ W L
    (fun b => if (ordinarySievePrimeProduct N Z).Coprime b then 1 else 0)
  simp only [BoundingSieve.siftedSum, fourthRowTripleGatedSieve, fourthRowTripleGatedS,
    sifted_iff_product_coprime, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  convert h using 1
  apply sum_congr rfl
  intro b _
  by_cases hb : (ordinarySievePrimeProduct N Z).Coprime b
  · simp only [if_pos hb, mul_one]
    exact if_pos hb
  · simp only [if_neg hb, mul_zero]
    exact if_neg hb

theorem fourthRowTripleGated_multSum {i : ℕ} (N q : ℕ) (he : Even N) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) :
    (fourthRowTripleGatedSieve N he δ Z W L).multSum q =
      ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) * (fourthRowTripleGatedAP N δ c q : ℝ) := by
  have h := fourthRowTripleGated_output_test N δ W L (fun b => if q ∣ b then 1 else 0)
  simp_rw [fourthRowTripleGated_AP_divisible]
  simpa only [BoundingSieve.multSum, fourthRowTripleGatedSieve, card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero] using h

theorem fourthRowTripleGated_remainder {i N q : ℕ} (he : Even N) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex)
    (hq : q ∣ ordinarySievePrimeProduct N Z) :
    (fourthRowTripleGatedSieve N he δ Z W L).rem q =
      fourthRowTripleGatedResidual N δ W L q -
        fourthRowTripleGatedMissing N δ W L q / (Nat.totient q : ℝ) := by
  rw [BoundingSieve.rem, fourthRowTripleGated_multSum]
  have hnu : (fourthRowTripleGatedSieve N he δ Z W L).nu q = 1 / (Nat.totient q : ℝ) :=
    goldbachNu_squarefree_eq_inv_totient
      ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd hq)
  rw [hnu]
  change _ - (1 / (Nat.totient q : ℝ)) * fourthRowTripleGatedX N δ W L = _
  rw [one_div_mul_eq_div]
  unfold fourthRowTripleGatedX fourthRowTripleGatedResidual fourthRowTripleGatedMissing
  simp only [sum_filter, sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro c _
  by_cases hc : (omega3CofactorValue c).Coprime q
  · simp only [if_pos hc, if_neg (not_not.mpr hc), zero_div, sub_zero]
    ring
  · rw [fourthRowTripleGated_AP_zero ((ordinarySievePrimeProduct_coprime N Z).of_dvd_left hq) hc]
    simp [hc]

theorem fourthRowTripleGated_mainSum {i : ℕ} (N D : ℕ) (he : Even N) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) :
    (fourthRowTripleGatedSieve N he δ Z W L).mainSum
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) =
        ordinaryRosserMainSum true N 1 D Z := by
  exact gamma16_family_main N D he δ Z W L

theorem fourthRowTripleGated_upper_finite {i N D : ℕ} (he : Even N) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex)
    (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    fourthRowTripleGatedS N δ Z W L ≤
      fourthRowTripleGatedX N δ W L * ordinaryRosserMainSum true N 1 D Z +
        fourthRowTripleGatedR1 N D δ Z W L + fourthRowTripleGatedR2 N D δ Z W L := by
  have herr : upperErrSum (fourthRowTripleGatedSieve N he δ Z W L) D
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) ≤
      fourthRowTripleGatedR1 N D δ Z W L + fourthRowTripleGatedR2 N D δ Z W L := by
    unfold upperErrSum fourthRowTripleGatedR1 fourthRowTripleGatedR2
    change (∑ q ∈ omega3SieveModuli N D Z, _) ≤ _
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro q hq
    rw [fourthRowTripleGated_remainder he δ Z W L (Nat.mem_divisors.mp (mem_filter.mp hq).1).1]
    have hn : 0 ≤ fourthRowTripleGatedMissing N δ W L q / (Nat.totient q : ℝ) :=
      div_nonneg (sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    have ha : |fourthRowTripleGatedResidual N δ W L q -
        fourthRowTripleGatedMissing N δ W L q / (Nat.totient q : ℝ)| ≤
        |fourthRowTripleGatedResidual N δ W L q| + fourthRowTripleGatedMissing N δ W L q / (Nat.totient q : ℝ) := by
      simpa only [abs_of_nonneg hn] using abs_sub (fourthRowTripleGatedResidual N δ W L q)
        (fourthRowTripleGatedMissing N δ W L q / (Nat.totient q : ℝ))
    have hw : |upperRosserWeight (ordinarySievePrimeProduct N Z) D q| ≤
        (3 : ℝ) ^ q.primeFactors.card :=
      (abs_upperRosserWeight_le_one _ _ _).trans (one_le_pow₀ (by norm_num))
    exact (mul_le_mul hw ha (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hprime : ∀ p ∈ (ordinarySievePrimeProduct N Z).primeFactors, p < D := by
    rw [ordinarySievePrimeProduct_primeFactors]
    intro p hp
    exact_mod_cast (mem_primeWindow.mp hp).2.2.2.trans_le hZ
  have hc := upperRosserWeight_certificate (ordinarySievePrimeProduct_squarefree N Z)
    (ordinarySievePrimeProduct_pos N Z).ne' hD hprime
  have hf := siftedSum_le_mainSum_add_upperErrSum_upperRosser
    (S := fourthRowTripleGatedSieve N he δ Z W L) D hc
  rw [fourthRowTripleGated_sifted] at hf
  change fourthRowTripleGatedS N δ Z W L ≤
    fourthRowTripleGatedX N δ W L * (fourthRowTripleGatedSieve N he δ Z W L).mainSum
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) +
      upperErrSum (fourthRowTripleGatedSieve N he δ Z W L) D
        (upperRosserWeight (ordinarySievePrimeProduct N Z) D) at hf
  rw [fourthRowTripleGated_mainSum] at hf
  linarith

end Wu2008DoubleSieve
