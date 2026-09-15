import MathlibNt.Wu2008DoubleSieve.LastPrimeFourDistribution
import MathlibNt.Wu2008DoubleSieve.Omega3SieveUpper

/-! The actual five-label last-prime sieve. Every profile prime is counted,
without output primality or varying-prime/output coprimality screens. -/
namespace Wu2008DoubleSieve.LastPrimeFour
open Finset
open scoped Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.LinearSieve

noncomputable def fourMass (N : ℕ) (e : Bool) : ℝ :=
  ∑ p ∈ labels N e, ((omega3ProfilePrimes N (lower N e p) (upper N e p)).card : ℝ)

noncomputable def fourOutputWeight (N : ℕ) (e : Bool) (b : ℕ) : ℝ :=
  ∑ p ∈ labels N e, (((omega3ProfilePrimes N (lower N e p) (upper N e p)).filter
    (fun r => N - cofactor p * r = b)).card : ℝ)
noncomputable def fourDivisible (N : ℕ) (e : Bool) (q : ℕ) : ℝ :=
  ∑ p ∈ labels N e, (((omega3ProfilePrimes N (lower N e p) (upper N e p)).filter
    (fun r => q ∣ N - cofactor p * r)).card : ℝ)
noncomputable def fourResidual (N : ℕ) (e : Bool) (q : ℕ) : ℝ :=
  ∑ p ∈ (labels N e).filter (fun p => (cofactor p).Coprime q),
    omega3ProfileError N q (cofactor p) (lower N e p) (upper N e p)
noncomputable def fourMissingMass (N : ℕ) (e : Bool) (q : ℕ) : ℝ :=
  ∑ p ∈ (labels N e).filter (fun p => ¬(cofactor p).Coprime q),
    ((omega3ProfilePrimes N (lower N e p) (upper N e p)).card : ℝ)
noncomputable def fourR2 (N : ℕ) (e : Bool) (D : ℕ) (Z : ℝ) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z,
    ((3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) * fourMissingMass N e q
noncomputable def fourSifted (N : ℕ) (e : Bool) (Z : ℝ) : ℝ :=
  ∑ p ∈ labels N e, (((omega3ProfilePrimes N (lower N e p) (upper N e p)).filter
    (fun r => Sifted N (N - cofactor p * r) Z)).card : ℝ)
noncomputable def fourBoundingSieve (N : ℕ) (e : Bool)
    (he : Even N) (Z : ℝ) : BoundingSieve where
  support := range (N + 1)
  prodPrimes := ordinarySievePrimeProduct N Z
  prodPrimes_squarefree := ordinarySievePrimeProduct_squarefree _ _
  weights := fourOutputWeight N e
  weights_nonneg := fun _ => sum_nonneg fun _ _ => Nat.cast_nonneg _
  totalMass := ∑ b ∈ range (N + 1), fourOutputWeight N e b
  nu := goldbachNu
  nu_mult := goldbachNu_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp hd => goldbachNu_lt_one_of_prime hp
    (ordinarySievePrimeProduct_prime_gt_two he Z hp hd)

theorem fourMass_nonneg (N : ℕ) (e : Bool) :
    0 ≤ fourMass N e := sum_nonneg fun _ _ => Nat.cast_nonneg _
theorem fourMissingMass_nonneg (N : ℕ) (e : Bool) (q : ℕ) :
    0 ≤ fourMissingMass N e q := sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem fourProfile_size {N : ℕ} {e : Bool} {p : Index}
    (hp : p ∈ labels N e) {r : ℕ}
    (hr : r ∈ omega3ProfilePrimes N (lower N e p) (upper N e p)) :
    cofactor p * r < N := by
  have hN : 0 < N := lt_of_lt_of_le (label_geometry hp).1 (label_le_N hp)
  exact ((upper_iff hN e p (label_geometry hp).1 r).mp (mem_filter.mp hr).2.2.2).2

theorem fourProfile_AP {N : ℕ} {e : Bool}
    {p : Index} (hp : p ∈ labels N e) (q : ℕ) :
    (omega3ProfilePrimes N (lower N e p) (upper N e p)).filter (fun r => Nat.ModEq q (cofactor p * r) N) =
    (omega3ProfilePrimes N (lower N e p) (upper N e p)).filter (fun r => q ∣ N - cofactor p * r) := by
  apply filter_congr
  intro r hr
  exact Nat.modEq_iff_dvd' (fourProfile_size hp hr).le

theorem fourProfile_AP_empty {N q : ℕ} {e : Bool}
    {p : Index} (hp : p ∈ labels N e)
    (hq : q.Coprime N) (hmq : ¬(cofactor p).Coprime q) :
    (omega3ProfilePrimes N (lower N e p) (upper N e p)).filter (fun r => Nat.ModEq q (cofactor p * r) N) = ∅ := by
  rw [fourProfile_AP hp q]
  apply eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hr, hd⟩ := mem_filter.mp hr
  have hgN : Nat.gcd (cofactor p) q ∣ N := by
    have hsub := (Nat.gcd_dvd_right (cofactor p) q).trans hd
    have hmul := (Nat.gcd_dvd_left (cofactor p) q).trans (dvd_mul_right _ r)
    simpa only [Nat.sub_add_cancel (fourProfile_size hp hr).le] using dvd_add hsub hmul
  have hg1 := Nat.dvd_gcd (Nat.gcd_dvd_right (cofactor p) q) hgN
  rw [hq.gcd_eq_one] at hg1
  exact hmq (Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hg1))

theorem four_remainder_identity {N q : ℕ} {e : Bool}
    (hq : q.Coprime N) :
    fourDivisible N e q - fourMass N e / (Nat.totient q : ℝ) =
      fourResidual N e q - fourMissingMass N e q / (Nat.totient q : ℝ) := by
  unfold fourDivisible fourMass fourResidual fourMissingMass
  simp only [sum_filter, sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← fourProfile_AP hp q]
  by_cases hmq : (cofactor p).Coprime q
  · simp only [if_pos hmq, if_neg (not_not.mpr hmq), zero_div, sub_zero]
    rfl
  · rw [fourProfile_AP_empty hp hq hmq]
    simp [hmq]

theorem fourOutputWeight_test (N : ℕ) (e : Bool) (f : ℕ → ℝ) :
    (∑ b ∈ range (N + 1), fourOutputWeight N e b * f b) =
      ∑ p ∈ labels N e, ∑ r ∈ omega3ProfilePrimes N (lower N e p) (upper N e p), f (N - cofactor p * r) := by
  unfold fourOutputWeight
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  have hb : N - cofactor p * r ∈ range (N + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
  rw [sum_eq_single (N - cofactor p * r)]
  · simp
  · intro b _ hne
    simp [Ne.symm hne]
  · exact fun hn => (hn hb).elim

theorem fourBoundingSieve_mass (N : ℕ) (e : Bool) (he : Even N) (Z : ℝ) :
    (∑ b ∈ (fourBoundingSieve N e he Z).support,
      (fourBoundingSieve N e he Z).weights b) = fourMass N e := by
  simpa only [fourBoundingSieve, fourMass, mul_one, sum_const, nsmul_eq_mul] using
    fourOutputWeight_test N e (fun _ => 1)

theorem fourBoundingSieve_totalMass (N : ℕ) (e : Bool) (he : Even N) (Z : ℝ) :
    (fourBoundingSieve N e he Z).totalMass = fourMass N e :=
  fourBoundingSieve_mass N e he Z

theorem fourBoundingSieve_multSum (N : ℕ) (e : Bool)
    (he : Even N) (Z : ℝ) (q : ℕ) :
    (fourBoundingSieve N e he Z).multSum q = fourDivisible N e q := by
  simpa only [BoundingSieve.multSum, fourBoundingSieve, fourDivisible,
    card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_ite, mul_one, mul_zero] using
    fourOutputWeight_test N e (fun b => if q ∣ b then 1 else 0)

theorem fourBoundingSieve_siftedSum (N : ℕ) (e : Bool) (he : Even N) (Z : ℝ) :
    (fourBoundingSieve N e he Z).siftedSum = fourSifted N e Z := by
  have h := fourOutputWeight_test N e
    (fun b => if (ordinarySievePrimeProduct N Z).Coprime b then 1 else 0)
  simp only [BoundingSieve.siftedSum, fourBoundingSieve, fourSifted,
    sifted_iff_product_coprime, card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  convert h using 1
  apply sum_congr rfl
  intro b _
  by_cases hb : (ordinarySievePrimeProduct N Z).Coprime b
  · simp only [if_pos hb, mul_one]; exact if_pos hb
  · simp only [if_neg hb, mul_zero]; exact if_neg hb

theorem fourBoundingSieve_rem {N q : ℕ} {e : Bool}
    (he : Even N) (Z : ℝ)
    (hq : q ∣ ordinarySievePrimeProduct N Z) :
    (fourBoundingSieve N e he Z).rem q =
      fourResidual N e q - fourMissingMass N e q / (Nat.totient q : ℝ) := by
  rw [BoundingSieve.rem, fourBoundingSieve_multSum]
  have hnu : (fourBoundingSieve N e he Z).nu q = 1 / (Nat.totient q : ℝ) :=
    goldbachNu_squarefree_eq_inv_totient
      ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd hq)
  rw [hnu, fourBoundingSieve_totalMass]
  change fourDivisible N e q - (1 / (Nat.totient q : ℝ)) * fourMass N e = _
  rw [one_div_mul_eq_div]
  exact four_remainder_identity ((ordinarySievePrimeProduct_coprime N Z).of_dvd_left hq)

theorem fourBoundingSieve_mainSum (N D : ℕ) (e : Bool) (he : Even N) (Z : ℝ) :
    (fourBoundingSieve N e he Z).mainSum
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) =
        ordinaryRosserMainSum true N 1 D Z := by
  unfold BoundingSieve.mainSum ordinaryRosserMainSum
  simp only [fourBoundingSieve, one_mul]
  apply sum_congr rfl
  intro q hq
  rw [goldbachNu_squarefree_eq_inv_totient
    ((ordinarySievePrimeProduct_squarefree N Z).squarefree_of_dvd (Nat.mem_divisors.mp hq).1)]
  simp only [ordinaryRosserWeight, if_true, one_mul, div_eq_mul_inv]

theorem fourBoundingSieve_error {N D : ℕ} {e : Bool}
    (he : Even N) (Z : ℝ) :
    upperErrSum (fourBoundingSieve N e he Z) D
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) ≤
        signedR1 N e D Z + fourR2 N e D Z := by
  unfold upperErrSum signedR1 fourR2
  change (∑ q ∈ omega3SieveModuli N D Z, _) ≤ _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro q hq
  have hd := (Nat.mem_divisors.mp (mem_filter.mp hq).1).1
  rw [fourBoundingSieve_rem he Z hd]
  have hmissing : 0 ≤ fourMissingMass N e q / (Nat.totient q : ℝ) :=
    div_nonneg (fourMissingMass_nonneg N e q) (Nat.cast_nonneg _)
  have habs := abs_sub (fourResidual N e q)
    (fourMissingMass N e q / (Nat.totient q : ℝ))
  rw [abs_of_nonneg hmissing] at habs
  have hw : |upperRosserWeight (ordinarySievePrimeProduct N Z) D q| ≤
      (3 : ℝ) ^ q.primeFactors.card :=
    (abs_upperRosserWeight_le_one _ _ _).trans (one_le_pow₀ (by norm_num))
  calc
    _ ≤ (3 : ℝ) ^ q.primeFactors.card *
        (|fourResidual N e q| + fourMissingMass N e q / (Nat.totient q : ℝ)) :=
      mul_le_mul hw habs (abs_nonneg _) (by positivity)
    _ = _ := by unfold fourResidual; ring

theorem four_sifted_upper_finite {N D : ℕ} {e : Bool}
    (he : Even N) (Z : ℝ)
    (hD : 1 < D) (hZ : Z ≤ (D : ℝ)) :
    fourSifted N e Z ≤ fourMass N e * ordinaryRosserMainSum true N 1 D Z +
      signedR1 N e D Z + fourR2 N e D Z := by
  have hprime : ∀ p ∈ (ordinarySievePrimeProduct N Z).primeFactors, p < D := by
    rw [ordinarySievePrimeProduct_primeFactors]
    intro p hp
    exact_mod_cast (mem_primeWindow.mp hp).2.2.2.trans_le hZ
  have hcert := upperRosserWeight_certificate (ordinarySievePrimeProduct_squarefree N Z)
    (ordinarySievePrimeProduct_pos N Z).ne' hD hprime
  have hf := siftedSum_le_mainSum_add_upperErrSum_upperRosser
    (S := fourBoundingSieve N e he Z) D hcert
  rw [fourBoundingSieve_siftedSum, fourBoundingSieve_totalMass] at hf
  change fourSifted N e Z ≤ fourMass N e *
    (fourBoundingSieve N e he Z).mainSum
      (upperRosserWeight (ordinarySievePrimeProduct N Z) D) +
        upperErrSum (fourBoundingSieve N e he Z) D
          (upperRosserWeight (ordinarySievePrimeProduct N Z) D) at hf
  rw [fourBoundingSieve_mainSum] at hf
  have herr := fourBoundingSieve_error (e := e) he (D := D) Z
  linarith
end Wu2008DoubleSieve.LastPrimeFour
