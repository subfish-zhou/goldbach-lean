import MathlibNt.Wu2008DoubleSieve.Gamma16Geometry
import MathlibNt.Wu2008DoubleSieve.Omega3SieveUpper
import MathlibNt.Wu2008DoubleSieve.Omega3R1Distribution

/-!
# Physical sieve on the lossless Gamma16 finite profile family

The finite-L parameter exposes the accepted layer APIs. The Gamma16
consumer fixes it to its encoded actual profiles, not to Omega3 labels.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple MathlibNt.SieveTheory.LinearSieve

noncomputable def gamma16FamilyX {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) : ℝ :=
  ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) * (omega3CofactorPrimeFibreLE N δ (5 / 2) c).card

noncomputable def gamma16FamilyS {i : ℕ} (N : ℕ) (δ Z : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) : ℝ :=
  ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) *
    (((omega3CofactorPrimeFibreLE N δ (5 / 2) c).filter
      (fun p => Sifted N (N - omega3CofactorValue c * p) Z)).card : ℝ)

noncomputable def gamma16FamilyWeight {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (b : ℕ) : ℝ :=
  ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) *
    (((omega3CofactorPrimeFibreLE N δ (5 / 2) c).filter
      (fun p => N - omega3CofactorValue c * p = b)).card : ℝ)

noncomputable def gamma16FamilyResidual {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (q : ℕ) : ℝ :=
  ∑ c ∈ L.filter (fun c => (omega3CofactorValue c).Coprime q),
    (convolutionCoeff W c.1 : ℝ) *
      ((omega3SieveAPCount N δ (5 / 2) c q : ℝ) -
        (omega3CofactorPrimeFibreLE N δ (5 / 2) c).card / (Nat.totient q : ℝ))

noncomputable def gamma16FamilyMissing {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (q : ℕ) : ℝ :=
  ∑ c ∈ L.filter (fun c => ¬(omega3CofactorValue c).Coprime q),
    (convolutionCoeff W c.1 : ℝ) * (omega3CofactorPrimeFibreLE N δ (5 / 2) c).card

noncomputable def gamma16FamilyR1 {i : ℕ} (N D : ℕ) (δ Z : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z, (3 : ℝ) ^ q.primeFactors.card *
    |gamma16FamilyResidual N δ W L q|

noncomputable def gamma16FamilyR2 {i : ℕ} (N D : ℕ) (δ Z : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z, ((3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) *
    gamma16FamilyMissing N δ W L q

noncomputable def gamma16FamilySieve {i : ℕ} (N : ℕ) (he : Even N) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) : BoundingSieve where
  support := range (N + 1)
  prodPrimes := ordinarySievePrimeProduct N Z
  prodPrimes_squarefree := ordinarySievePrimeProduct_squarefree _ _
  weights := gamma16FamilyWeight N δ W L
  weights_nonneg := fun _ => sum_nonneg fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  totalMass := gamma16FamilyX N δ W L
  nu := goldbachNu
  nu_mult := goldbachNu_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp hd => goldbachNu_lt_one_of_prime hp
    (ordinarySievePrimeProduct_prime_gt_two he Z hp hd)

theorem gamma16_family_output_test {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (f : ℕ → ℝ) :
    (∑ b ∈ range (N + 1), gamma16FamilyWeight N δ W L b * f b) =
      ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) *
        ∑ p ∈ omega3CofactorPrimeFibreLE N δ (5 / 2) c, f (N - omega3CofactorValue c * p) := by
  unfold gamma16FamilyWeight
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_sum, sum_mul]
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

theorem gamma16_family_sifted {i : ℕ} (N : ℕ) (he : Even N) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) :
    (gamma16FamilySieve N he δ Z W L).siftedSum = gamma16FamilyS N δ Z W L := by
  have h := gamma16_family_output_test N δ W L
    (fun b => if (ordinarySievePrimeProduct N Z).Coprime b then 1 else 0)
  simp only [BoundingSieve.siftedSum, gamma16FamilySieve, gamma16FamilyS,
    sifted_iff_product_coprime, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  convert h using 1
  apply sum_congr rfl
  intro b _
  by_cases hb : (ordinarySievePrimeProduct N Z).Coprime b
  · simp only [if_pos hb, mul_one]
    exact if_pos hb
  · simp only [if_neg hb, mul_zero]
    exact if_neg hb

theorem gamma16_family_remainder {i N q : ℕ} (he : Even N) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex)
    (hq : q ∣ ordinarySievePrimeProduct N Z) :
    (gamma16FamilySieve N he δ Z W L).rem q =
      gamma16FamilyResidual N δ W L q - gamma16FamilyMissing N δ W L q / (Nat.totient q : ℝ) := by
  have hm : (gamma16FamilySieve N he δ Z W L).multSum q =
      ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) * (omega3SieveAPCount N δ (5 / 2) c q : ℝ) := by
    have h := gamma16_family_output_test N δ W L (fun b => if q ∣ b then 1 else 0)
    simp_rw [omega3SieveAPCount_eq_divisible]
    simpa only [BoundingSieve.multSum, gamma16FamilySieve, card_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero] using h
  rw [BoundingSieve.rem, hm]
  have hnu : (gamma16FamilySieve N he δ Z W L).nu q = 1 / (Nat.totient q : ℝ) :=
    goldbachNu_squarefree_eq_inv_totient
      ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd hq)
  rw [hnu]
  change _ - (1 / (Nat.totient q : ℝ)) * gamma16FamilyX N δ W L = _
  rw [one_div_mul_eq_div]
  unfold gamma16FamilyX gamma16FamilyResidual gamma16FamilyMissing
  simp only [sum_filter, sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro c _
  by_cases hc : (omega3CofactorValue c).Coprime q
  · simp only [if_pos hc, if_neg (not_not.mpr hc), zero_div, sub_zero]
    ring
  · rw [omega3SieveAPCount_eq_zero_of_not_coprime
      ((ordinarySievePrimeProduct_coprime N Z).of_dvd_left hq) hc]
    simp [hc]

theorem gamma16_family_main {i : ℕ} (N D : ℕ) (he : Even N) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex) :
    (gamma16FamilySieve N he δ Z W L).mainSum
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) =
        ordinaryRosserMainSum true N 1 D Z := by
  unfold BoundingSieve.mainSum ordinaryRosserMainSum
  simp only [gamma16FamilySieve, one_mul]
  apply sum_congr rfl
  intro q hq
  rw [goldbachNu_squarefree_eq_inv_totient
    ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd (Nat.mem_divisors.mp hq).1)]
  simp only [ordinaryRosserWeight, if_true, one_mul, div_eq_mul_inv]

theorem gamma16_family_upper_finite {i N D : ℕ} (he : Even N) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex)
    (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    gamma16FamilyS N δ Z W L ≤
      gamma16FamilyX N δ W L * ordinaryRosserMainSum true N 1 D Z +
        gamma16FamilyR1 N D δ Z W L + gamma16FamilyR2 N D δ Z W L := by
  have herr : upperErrSum (gamma16FamilySieve N he δ Z W L) D
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) ≤
      gamma16FamilyR1 N D δ Z W L + gamma16FamilyR2 N D δ Z W L := by
    unfold upperErrSum gamma16FamilyR1 gamma16FamilyR2
    change (∑ q ∈ omega3SieveModuli N D Z, _) ≤ _
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro q hq
    rw [gamma16_family_remainder he δ Z W L (Nat.mem_divisors.mp (mem_filter.mp hq).1).1]
    have hn : 0 ≤ gamma16FamilyMissing N δ W L q / (Nat.totient q : ℝ) :=
      div_nonneg (sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    have ha : |gamma16FamilyResidual N δ W L q -
        gamma16FamilyMissing N δ W L q / (Nat.totient q : ℝ)| ≤
        |gamma16FamilyResidual N δ W L q| + gamma16FamilyMissing N δ W L q / (Nat.totient q : ℝ) := by
      simpa only [abs_of_nonneg hn] using abs_sub (gamma16FamilyResidual N δ W L q)
        (gamma16FamilyMissing N δ W L q / (Nat.totient q : ℝ))
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
    (S := gamma16FamilySieve N he δ Z W L) D hc
  rw [gamma16_family_sifted] at hf
  change gamma16FamilyS N δ Z W L ≤
    gamma16FamilyX N δ W L * (gamma16FamilySieve N he δ Z W L).mainSum
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) +
      upperErrSum (gamma16FamilySieve N he δ Z W L) D
        (upperRosserWeight (ordinarySievePrimeProduct N Z) D) at hf
  rw [gamma16_family_main] at hf
  change gamma16FamilyS N δ Z W L ≤
    gamma16FamilyX N δ W L * ordinaryRosserMainSum true N 1 D Z + _ at hf
  linarith

theorem gamma16_actual_family {i : ℕ} (N : ℕ) (δ Z : ℝ) (W : Fin i → Finset ℕ) :
    gamma16FamilyX N δ W (gamma16EncodedProfiles N δ W) = gamma16X N δ W ∧
      gamma16FamilyS N δ Z W (gamma16EncodedProfiles N δ W) = gamma16S N δ Z W := by
  constructor
  · exact gamma16_encoded_sum N δ W _
  · rw [gamma16FamilyS, gamma16_encoded_sum]
    simp only [gamma16S, gamma16PrimeFibre, gamma16_encode_value]

end Wu2008DoubleSieve
