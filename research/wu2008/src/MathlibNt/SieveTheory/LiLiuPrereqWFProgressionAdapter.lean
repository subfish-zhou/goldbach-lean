import MathlibNt.SieveTheory.LiLiuPrereqWFUnmaskedRemainder
import Mathlib.Data.Nat.ModEq

/-!
# The reduced-residue discrepancy and its actual coprime-mass correction

Fouvry's discrepancy subtracts the modulus-dependent coprime mass, not a
fixed `X / φ(d)`. The identity below displays that difference explicitly.
For a set of primes its correction is bounded by finite harmonic sums; no
equidistribution theorem is asserted or assumed.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction
open scoped Classical

noncomputable def primeCoprimeMass (I : Finset ℕ) (d : ℕ) : ℝ :=
  ∑ p ∈ I, if p.Coprime d then 1 else 0

noncomputable def primeProgressionDiscrepancy (I : Finset ℕ) (a d : ℕ) : ℝ :=
  (∑ p ∈ I, if Nat.ModEq d p a then 1 else 0) -
    primeCoprimeMass I d * (d.totient : ℝ)⁻¹

noncomputable def familyProgressionDiscrepancy (upper : Bool) (P : Finset ℕ)
    (D ε : ℝ) (label : ℕ → ℕ) (I : Finset ℕ) (a : ℕ) : ℝ :=
  ∑ t ∈ signedTags upper P D ε label,
    ∑ d ∈ (Icc 1 ⌊D ^ (1 + ε + ε ^ 9)⌋₊).filter (fun d => d.Coprime a),
      signedFamilyTerm upper P D ε t d * primeProgressionDiscrepancy I a d

noncomputable def familyCoprimeCorrection (upper : Bool) (P : Finset ℕ)
    (D ε : ℝ) (label : ℕ → ℕ) (I : Finset ℕ) (a : ℕ) (X : ℝ) : ℝ :=
  ∑ t ∈ signedTags upper P D ε label,
    ∑ d ∈ (Icc 1 ⌊D ^ (1 + ε + ε ^ 9)⌋₊).filter (fun d => d.Coprime a),
      signedFamilyTerm upper P D ε t d *
        ((primeCoprimeMass I d - X) * (d.totient : ℝ)⁻¹)

theorem signedFamilyTerm_coprime_of_ne_zero (upper : Bool) (P : Finset ℕ)
    (D ε : ℝ) (t : List ℕ) {a d : ℕ}
    (hP : ∀ p ∈ P, p.Coprime a) (hd : signedFamilyTerm upper P D ε t d ≠ 0) :
    d.Coprime a := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd (by simp)
  apply Nat.coprime_of_dvd
  intro p hp hpd
  exact hp.coprime_iff_not_dvd.mp
    (hP p (signedFamilyTerm_primeSupported upper P D ε t d hd
      (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd0⟩)))

/-- The original shifted count is an actual progression count, including the
endpoint `p = a`; no sieve or distribution estimate enters this identity. -/
theorem shifted_sequence_progression (I : Finset ℕ) (a d : ℕ)
    (hI : ∀ p ∈ I, p ≤ a) :
    sequenceDivisibility I (fun p => a - p) d =
      ∑ p ∈ I, if Nat.ModEq d p a then 1 else 0 := by
  apply sum_congr rfl
  intro p hp
  simp only [Nat.modEq_iff_dvd' (hI p hp)]

/-- Full-modulus transport is not silently identified with Fouvry's
discrepancy: its additional coprime-mass term is retained exactly.
The reduced-modulus restriction follows from the ORIGINAL coefficient support. -/
theorem fullSignedFamilyRemainder_progression_identity (upper : Bool) (P : Finset ℕ)
    (D ε : ℝ) (label : ℕ → ℕ) (I : Finset ℕ) (a : ℕ) (X : ℝ)
    (hP : ∀ p ∈ P, p.Coprime a) (hI : ∀ p ∈ I, p ≤ a) :
    fullSignedFamilyRemainder upper P D ε label I (fun p => a - p) X
        (progressionDensity a) =
      familyProgressionDiscrepancy upper P D ε label I a +
        familyCoprimeCorrection upper P D ε label I a X := by
  unfold fullSignedFamilyRemainder familyProgressionDiscrepancy familyCoprimeCorrection
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  rw [← sum_add_distrib, sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases hd : d.Coprime a
  · simp only [sequenceRemainder, progressionDensity,
      ArithmeticFunction.coe_mk, primeProgressionDiscrepancy,
      shifted_sequence_progression I a d hI]
    rw [if_pos hd, if_pos hd]
    ring
  · have hz : signedFamilyTerm upper P D ε t d = 0 := by
      by_contra hn
      exact hd (signedFamilyTerm_coprime_of_ne_zero upper P D ε t hP hn)
    simp [hd, hz]

theorem primeCoprimeMass_identity (I : Finset ℕ) (hI : ∀ p ∈ I, p.Prime) (d : ℕ) :
    primeCoprimeMass I d =
      (I.card : ℝ) - ∑ p ∈ I, if p ∣ d then 1 else 0 := by
  rw [primeCoprimeMass, show (I.card : ℝ) = ∑ _p ∈ I, (1 : ℝ) by simp,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  simp only [(hI p hp).coprime_iff_not_dvd]
  split_ifs <;> norm_num

/-- Only the actual prime entries dividing the modulus are removed from the
coprime mass. Their total inverse-totient cost is logarithmic, not proportional
to the cardinality of the prime sequence. -/
theorem prime_divisor_mass_le (I : Finset ℕ) (hI : ∀ p ∈ I, p.Prime)
    (N T : ℕ) (hN : ∀ p ∈ I, p ≤ N) :
    (∑ d ∈ Icc 1 T, (∑ p ∈ I, if p ∣ d then (1 : ℝ) else 0) *
      (d.totient : ℝ)⁻¹) ≤
        PrimeSquareMass.harmonicSum N ^ 2 * PrimeSquareMass.harmonicSum T ^ 2 := by
  have hsub : I ⊆ Icc 1 N :=
    fun p hp => mem_Icc.mpr ⟨(hI p hp).pos, hN p hp⟩
  calc
    _ = ∑ p ∈ I, ∑ d ∈ (Icc 1 T).filter (fun d => p ∣ d), (d.totient : ℝ)⁻¹ := by
      simp only [sum_mul, sum_filter, ite_mul, one_mul, zero_mul]
      rw [sum_comm]
    _ ≤ ∑ p ∈ I, (p.totient : ℝ)⁻¹ * PrimeSquareMass.harmonicSum T ^ 2 :=
      sum_le_sum fun p hp =>
        PrimeSquareMass.sum_inv_totient_multiples_le T p (hI p hp).pos
    _ = (∑ p ∈ I, (p.totient : ℝ)⁻¹) * PrimeSquareMass.harmonicSum T ^ 2 :=
      (sum_mul ..).symm
    _ ≤ (∑ p ∈ Icc 1 N, (p.totient : ℝ)⁻¹) * PrimeSquareMass.harmonicSum T ^ 2 :=
      mul_le_mul_of_nonneg_right
        (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)) (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (PrimeSquareMass.sum_inv_totient_le_harmonic_sq N) (sq_nonneg _)

/-- A bounded unmasked coefficient needs no squarefree restriction for this
prime-sequence coprime-mass estimate. -/
theorem coprimeCorrection_abs_le (f : ArithmeticFunction ℝ) (hf : BoundedOne f)
    (I : Finset ℕ) (hI : ∀ p ∈ I, p.Prime) (N T a : ℕ)
    (hN : ∀ p ∈ I, p ≤ N) (X : ℝ) :
    |∑ d ∈ (Icc 1 T).filter (fun d => d.Coprime a),
      f d * ((primeCoprimeMass I d - X) * (d.totient : ℝ)⁻¹)| ≤
        (|(I.card : ℝ) - X| + PrimeSquareMass.harmonicSum N ^ 2) *
          PrimeSquareMass.harmonicSum T ^ 2 := by
  have hc0 (d : ℕ) : 0 ≤ ∑ p ∈ I, if p ∣ d then (1 : ℝ) else 0 :=
    sum_nonneg fun p _ => by split_ifs <;> positivity
  have hmass (d : ℕ) :
      |primeCoprimeMass I d - X| ≤
        |(I.card : ℝ) - X| + ∑ p ∈ I, if p ∣ d then (1 : ℝ) else 0 := by
    rw [primeCoprimeMass_identity I hI d]
    have heq : (I.card : ℝ) - (∑ p ∈ I, if p ∣ d then (1 : ℝ) else 0) - X =
        ((I.card : ℝ) - X) + -(∑ p ∈ I, if p ∣ d then (1 : ℝ) else 0) := by ring
    rw [heq]
    simpa only [abs_neg, abs_of_nonneg (hc0 d)] using abs_add_le
      ((I.card : ℝ) - X) (-(∑ p ∈ I, if p ∣ d then (1 : ℝ) else 0))
  calc
    _ ≤ ∑ d ∈ (Icc 1 T).filter (fun d => d.Coprime a),
        |f d * ((primeCoprimeMass I d - X) * (d.totient : ℝ)⁻¹)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (Icc 1 T).filter (fun d => d.Coprime a),
        (|(I.card : ℝ) - X| + ∑ p ∈ I, if p ∣ d then (1 : ℝ) else 0) *
          (d.totient : ℝ)⁻¹ := by
      apply sum_le_sum
      intro d _
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (d.totient : ℝ)⁻¹)]
      calc
        _ ≤ 1 * (|primeCoprimeMass I d - X| * (d.totient : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right (hf d) (by positivity)
        _ ≤ _ := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right (hmass d) (by positivity)
    _ ≤ ∑ d ∈ Icc 1 T,
        (|(I.card : ℝ) - X| + ∑ p ∈ I, if p ∣ d then (1 : ℝ) else 0) *
          (d.totient : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun d _ _ => by
        exact mul_nonneg (add_nonneg (abs_nonneg _) (hc0 d)) (by positivity))
    _ = |(I.card : ℝ) - X| * (∑ d ∈ Icc 1 T, (d.totient : ℝ)⁻¹) +
        ∑ d ∈ Icc 1 T, (∑ p ∈ I, if p ∣ d then (1 : ℝ) else 0) * (d.totient : ℝ)⁻¹ := by
      simp only [add_mul, sum_add_distrib, mul_sum]
    _ ≤ |(I.card : ℝ) - X| * PrimeSquareMass.harmonicSum T ^ 2 +
        PrimeSquareMass.harmonicSum N ^ 2 * PrimeSquareMass.harmonicSum T ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (PrimeSquareMass.sum_inv_totient_le_harmonic_sq T)
          (abs_nonneg _)) (prime_divisor_mass_le I hI N T hN)
    _ = _ := by ring

theorem familyCoprimeCorrection_abs_le (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (label : ℕ → ℕ) (hD : 2 ≤ D) (hε : 0 < ε)
    (hεsmall : ε < 1 / 8) (I : Finset ℕ) (hI : ∀ p ∈ I, p.Prime)
    (N a : ℕ) (hN : ∀ p ∈ I, p ≤ N) (X : ℝ) :
    |familyCoprimeCorrection upper P D ε label I a X| ≤
      ((signedTags upper P D ε label).card : ℝ) *
        ((|(I.card : ℝ) - X| + PrimeSquareMass.harmonicSum N ^ 2) *
          PrimeSquareMass.harmonicSum ⌊D ^ (1 + ε + ε ^ 9)⌋₊ ^ 2) := by
  unfold familyCoprimeCorrection
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro t ht
  exact coprimeCorrection_abs_le _ (signedTags_common_wellFactorable upper P label
    hD hε hεsmall t ht).2.1 I hI N _ a hN X

noncomputable def primeProgressionTransportCost (upper : Bool) (P : Finset ℕ)
    (D ε : ℝ) (label : ℕ → ℕ) (I : Finset ℕ) (N : ℕ) (X : ℝ) : ℝ :=
  fullModulusTransportCost upper P D ε label N X +
    ((signedTags upper P D ε label).card : ℝ) *
      ((|(I.card : ℝ) - X| + PrimeSquareMass.harmonicSum N ^ 2) *
        PrimeSquareMass.harmonicSum ⌊D ^ (1 + ε + ε ^ 9)⌋₊ ^ 2)

/-- The actual prime-shift consumer, with the full reduced-residue discrepancy
and both corrections paid. When `X = #I` the fixed-mass discrepancy vanishes.
Any analytic distribution bound on the displayed signed discrepancy is a
separate theorem; it has not been inserted as a hypothesis here. -/
theorem signedFamily_reduced_prime_sequence_sieve (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε : ℝ} (hD : 2 ≤ D)
    (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D)
    (I : Finset ℕ) (hIprime : ∀ p ∈ I, p.Prime) (N : ℕ)
    (hI : ∀ p ∈ I, p < N) (hPN : ∀ p ∈ P, p.Coprime N) (X : ℝ) :
    let label := geometricSieveLabel D ε
    let g := progressionDensity N
    X * signedFamilyDensity false P D ε label g +
        familyProgressionDiscrepancy false P D ε label I N -
        primeProgressionTransportCost false P D ε label I N X ≤
          sequenceSifted I (fun p => N - p) P ∧
      sequenceSifted I (fun p => N - p) P ≤
        X * signedFamilyDensity true P D ε label g +
          familyProgressionDiscrepancy true P D ε label I N +
          primeProgressionTransportCost true P D ε label I N X := by
  dsimp only
  let label := geometricSieveLabel D ε
  have hle : ∀ p ∈ I, p ≤ N := fun p hp => (hI p hp).le
  have hs := signedFamily_full_shifted_sieve P hP hD hε hεsmall hcut I N hI X
  have hl := fullSignedFamilyRemainder_progression_identity false P D ε label I N X hPN hle
  have hu := fullSignedFamilyRemainder_progression_identity true P D ε label I N X hPN hle
  have hcl := abs_le.mp
    (familyCoprimeCorrection_abs_le false P label hD hε hεsmall I hIprime N N hle X)
  have hcu := abs_le.mp
    (familyCoprimeCorrection_abs_le true P label hD hε hεsmall I hIprime N N hle X)
  change _ ≤ sequenceSifted I (fun p => N - p) P ∧
    sequenceSifted I (fun p => N - p) P ≤ _ at hs
  change X * signedFamilyDensity false P D ε label (progressionDensity N) + _ - _ ≤ _ ∧
    _ ≤ X * signedFamilyDensity true P D ε label (progressionDensity N) + _ + _
  unfold primeProgressionTransportCost
  constructor <;> linarith [hs.1, hs.2]

#check fullSignedFamilyRemainder_progression_identity
#print axioms fullSignedFamilyRemainder_progression_identity
#check prime_divisor_mass_le
#print axioms prime_divisor_mass_le
#check familyCoprimeCorrection_abs_le
#print axioms familyCoprimeCorrection_abs_le
#check signedFamily_reduced_prime_sequence_sieve
#print axioms signedFamily_reduced_prime_sequence_sieve

end MathlibNt.SieveTheory.LiLiuPrereqWF
