import MathlibNt.Wu2008DoubleSieve.SeventhEighthClassicalMass
import MathlibNt.Wu2008DoubleSieve.Omega3SieveUpper

/-! The labelled pair-profile sieve. No coprimality masks are added to the
varying prime or its output. Only the exact AP split uses a coprime mask. -/
namespace Wu2008DoubleSieve.SeventhEighth
open Finset
open scoped Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.LinearSieve

noncomputable def classicalOutputWeight (N : ℕ) (S : Finset (ℕ × ℕ)) (b : ℕ) : ℝ :=
  ∑ p ∈ S, (((classicalProfile N p).filter
    (fun r => N - ninthPairProduct p * r = b)).card : ℝ)
noncomputable def classicalDivisible (N : ℕ) (S : Finset (ℕ × ℕ)) (q : ℕ) : ℝ :=
  ∑ p ∈ S, (((classicalProfile N p).filter
    (fun r => q ∣ N - ninthPairProduct p * r)).card : ℝ)
noncomputable def classicalResidual (N : ℕ) (S : Finset (ℕ × ℕ)) (q : ℕ) : ℝ :=
  ∑ p ∈ S.filter (fun p => (ninthPairProduct p).Coprime q),
    omega3ProfileError N q (ninthPairProduct p) ((p.2 : ℝ) - 1)
      (ninthProfileUpper N (ninthPairProduct p))
noncomputable def classicalMissingMass (N : ℕ) (S : Finset (ℕ × ℕ)) (q : ℕ) : ℝ :=
  ∑ p ∈ S.filter (fun p => ¬(ninthPairProduct p).Coprime q),
    ((classicalProfile N p).card : ℝ)
noncomputable def classicalR2 (N : ℕ) (S : Finset (ℕ × ℕ)) (D : ℕ) (Z : ℝ) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z,
    ((3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) * classicalMissingMass N S q
noncomputable def classicalSifted (N : ℕ) (S : Finset (ℕ × ℕ)) (Z : ℝ) : ℝ :=
  ∑ p ∈ S, (((classicalProfile N p).filter
    (fun r => Sifted N (N - ninthPairProduct p * r) Z)).card : ℝ)
noncomputable def classicalBoundingSieve (N : ℕ) (S : Finset (ℕ × ℕ))
    (he : Even N) (Z : ℝ) : BoundingSieve where
  support := range (N + 1)
  prodPrimes := ordinarySievePrimeProduct N Z
  prodPrimes_squarefree := ordinarySievePrimeProduct_squarefree _ _
  weights := classicalOutputWeight N S
  weights_nonneg := fun _ => sum_nonneg fun _ _ => Nat.cast_nonneg _
  totalMass := classicalMass N S
  nu := goldbachNu
  nu_mult := goldbachNu_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp hd => goldbachNu_lt_one_of_prime hp
    (ordinarySievePrimeProduct_prime_gt_two he Z hp hd)

theorem classicalMass_nonneg (N : ℕ) (S : Finset (ℕ × ℕ)) :
    0 ≤ classicalMass N S := sum_nonneg fun _ _ => Nat.cast_nonneg _
theorem classicalMissingMass_nonneg (N : ℕ) (S : Finset (ℕ × ℕ)) (q : ℕ) :
    0 ≤ classicalMissingMass N S q := sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem classicalProfile_size {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {p : ℕ × ℕ} (hp : p ∈ S)
    {r : ℕ} (hr : r ∈ classicalProfile N p) : ninthPairProduct p * r < N := by
  obtain ⟨ha, hb, _, _, hs, _⟩ := hS p hp
  exact (ninthProfileUpper_nat_iff (by omega) (Nat.mul_pos ha.pos hb.pos)).mp
    (mem_filter.mp hr).2.2.2

theorem classicalProfile_AP {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {p : ℕ × ℕ} (hp : p ∈ S) (q : ℕ) :
    (classicalProfile N p).filter (fun r => Nat.ModEq q (ninthPairProduct p * r) N) =
    (classicalProfile N p).filter (fun r => q ∣ N - ninthPairProduct p * r) := by
  apply filter_congr
  intro r hr
  exact Nat.modEq_iff_dvd' (classicalProfile_size hS hp hr).le

theorem classicalProfile_AP_empty {N q : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) {p : ℕ × ℕ} (hp : p ∈ S)
    (hq : q.Coprime N) (hmq : ¬(ninthPairProduct p).Coprime q) :
    (classicalProfile N p).filter (fun r => Nat.ModEq q (ninthPairProduct p * r) N) = ∅ := by
  rw [classicalProfile_AP hS hp q]
  apply eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hr, hd⟩ := mem_filter.mp hr
  have hgN : Nat.gcd (ninthPairProduct p) q ∣ N := by
    have hsub := (Nat.gcd_dvd_right (ninthPairProduct p) q).trans hd
    have hmul := (Nat.gcd_dvd_left (ninthPairProduct p) q).trans (dvd_mul_right _ r)
    simpa only [Nat.sub_add_cancel (classicalProfile_size hS hp hr).le] using dvd_add hsub hmul
  have hg1 := Nat.dvd_gcd (Nat.gcd_dvd_right (ninthPairProduct p) q) hgN
  rw [hq.gcd_eq_one] at hg1
  exact hmq (Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hg1))

theorem classical_remainder_identity {N q : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) (hq : q.Coprime N) :
    classicalDivisible N S q - classicalMass N S / (Nat.totient q : ℝ) =
      classicalResidual N S q - classicalMissingMass N S q / (Nat.totient q : ℝ) := by
  unfold classicalDivisible classicalMass classicalResidual classicalMissingMass
  simp only [sum_filter, sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← classicalProfile_AP hS hp q]
  by_cases hmq : (ninthPairProduct p).Coprime q
  · simp only [if_pos hmq, if_neg (not_not.mpr hmq), zero_div, sub_zero]
    rfl
  · rw [classicalProfile_AP_empty hS hp hq hmq]
    simp [hmq]

theorem classicalOutputWeight_test (N : ℕ) (S : Finset (ℕ × ℕ)) (f : ℕ → ℝ) :
    (∑ b ∈ range (N + 1), classicalOutputWeight N S b * f b) =
      ∑ p ∈ S, ∑ r ∈ classicalProfile N p, f (N - ninthPairProduct p * r) := by
  unfold classicalOutputWeight
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  have hb : N - ninthPairProduct p * r ∈ range (N + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
  rw [sum_eq_single (N - ninthPairProduct p * r)]
  · simp
  · intro b _ hne
    simp [Ne.symm hne]
  · exact fun hn => (hn hb).elim

theorem classicalBoundingSieve_mass (N : ℕ) (S : Finset (ℕ × ℕ)) (he : Even N) (Z : ℝ) :
    (∑ b ∈ (classicalBoundingSieve N S he Z).support,
      (classicalBoundingSieve N S he Z).weights b) = classicalMass N S := by
  simpa only [classicalBoundingSieve, classicalMass, mul_one, sum_const, nsmul_eq_mul] using
    classicalOutputWeight_test N S (fun _ => 1)

theorem classicalBoundingSieve_multSum (N : ℕ) (S : Finset (ℕ × ℕ))
    (he : Even N) (Z : ℝ) (q : ℕ) :
    (classicalBoundingSieve N S he Z).multSum q = classicalDivisible N S q := by
  simpa only [BoundingSieve.multSum, classicalBoundingSieve, classicalDivisible,
    card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_ite, mul_one, mul_zero] using
    classicalOutputWeight_test N S (fun b => if q ∣ b then 1 else 0)

theorem classicalBoundingSieve_siftedSum (N : ℕ) (S : Finset (ℕ × ℕ)) (he : Even N) (Z : ℝ) :
    (classicalBoundingSieve N S he Z).siftedSum = classicalSifted N S Z := by
  have h := classicalOutputWeight_test N S
    (fun b => if (ordinarySievePrimeProduct N Z).Coprime b then 1 else 0)
  simp only [BoundingSieve.siftedSum, classicalBoundingSieve, classicalSifted,
    sifted_iff_product_coprime, card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  convert h using 1
  apply sum_congr rfl
  intro b _
  by_cases hb : (ordinarySievePrimeProduct N Z).Coprime b
  · simp only [if_pos hb, mul_one]; exact if_pos hb
  · simp only [if_neg hb, mul_zero]; exact if_neg hb

theorem classicalBoundingSieve_rem {N q : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) (he : Even N) (Z : ℝ)
    (hq : q ∣ ordinarySievePrimeProduct N Z) :
    (classicalBoundingSieve N S he Z).rem q =
      classicalResidual N S q - classicalMissingMass N S q / (Nat.totient q : ℝ) := by
  rw [BoundingSieve.rem, classicalBoundingSieve_multSum]
  have hnu : (classicalBoundingSieve N S he Z).nu q = 1 / (Nat.totient q : ℝ) :=
    goldbachNu_squarefree_eq_inv_totient
      ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd hq)
  rw [hnu]
  change classicalDivisible N S q - (1 / (Nat.totient q : ℝ)) * classicalMass N S = _
  rw [one_div_mul_eq_div]
  exact classical_remainder_identity hS ((ordinarySievePrimeProduct_coprime N Z).of_dvd_left hq)

theorem classicalBoundingSieve_mainSum (N D : ℕ) (S : Finset (ℕ × ℕ)) (he : Even N) (Z : ℝ) :
    (classicalBoundingSieve N S he Z).mainSum
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) =
        ordinaryRosserMainSum true N 1 D Z := by
  unfold BoundingSieve.mainSum ordinaryRosserMainSum
  simp only [classicalBoundingSieve, one_mul]
  apply sum_congr rfl
  intro q hq
  rw [goldbachNu_squarefree_eq_inv_totient
    ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd (Nat.mem_divisors.mp hq).1)]
  simp only [ordinaryRosserWeight, if_true, one_mul, div_eq_mul_inv]

theorem classicalBoundingSieve_error {N D : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) (he : Even N) (Z : ℝ) :
    upperErrSum (classicalBoundingSieve N S he Z) D
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) ≤
        classicalPairR1 N S D Z + classicalR2 N S D Z := by
  unfold upperErrSum classicalPairR1 classicalR2
  change (∑ q ∈ omega3SieveModuli N D Z, _) ≤ _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro q hq
  have hd := (Nat.mem_divisors.mp (mem_filter.mp hq).1).1
  rw [classicalBoundingSieve_rem hS he Z hd]
  have hmissing : 0 ≤ classicalMissingMass N S q / (Nat.totient q : ℝ) :=
    div_nonneg (classicalMissingMass_nonneg N S q) (Nat.cast_nonneg _)
  have habs := abs_sub (classicalResidual N S q)
    (classicalMissingMass N S q / (Nat.totient q : ℝ))
  rw [abs_of_nonneg hmissing] at habs
  have hw : |upperRosserWeight (ordinarySievePrimeProduct N Z) D q| ≤
      (3 : ℝ) ^ q.primeFactors.card :=
    (abs_upperRosserWeight_le_one _ _ _).trans (one_le_pow₀ (by norm_num))
  calc
    _ ≤ (3 : ℝ) ^ q.primeFactors.card *
        (|classicalResidual N S q| + classicalMissingMass N S q / (Nat.totient q : ℝ)) :=
      mul_le_mul hw habs (abs_nonneg _) (by positivity)
    _ = _ := by unfold classicalResidual; ring

theorem classical_sifted_upper_finite {N D : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : ClassicalPairGeometry N S) (he : Even N) (Z : ℝ)
    (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    classicalSifted N S Z ≤ classicalMass N S * ordinaryRosserMainSum true N 1 D Z +
      classicalPairR1 N S D Z + classicalR2 N S D Z := by
  have hprime : ∀ p ∈ (ordinarySievePrimeProduct N Z).primeFactors, p < D := by
    rw [ordinarySievePrimeProduct_primeFactors]
    intro p hp
    exact_mod_cast (mem_primeWindow.mp hp).2.2.2.trans_le hZ
  have hcert := upperRosserWeight_certificate (ordinarySievePrimeProduct_squarefree N Z)
    (ordinarySievePrimeProduct_pos N Z).ne' hD hprime
  have hf := siftedSum_le_mainSum_add_upperErrSum_upperRosser
    (S := classicalBoundingSieve N S he Z) D hcert
  rw [classicalBoundingSieve_siftedSum] at hf
  change classicalSifted N S Z ≤ classicalMass N S *
    (classicalBoundingSieve N S he Z).mainSum
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) +
        upperErrSum (classicalBoundingSieve N S he Z) D
          (upperRosserWeight (ordinarySievePrimeProduct N Z) D) at hf
  rw [classicalBoundingSieve_mainSum] at hf
  have herr := classicalBoundingSieve_error hS he (D := D) Z
  linarith
end Wu2008DoubleSieve.SeventhEighth
