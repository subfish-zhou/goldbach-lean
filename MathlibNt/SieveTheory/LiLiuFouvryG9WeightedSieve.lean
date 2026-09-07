import MathlibNt.SieveTheory.LiLiuPrereqWFExternalFamily

/-!
# Nonnegative weighted finite sieve for the existing external WF family

Indices are retained: entries may be zero or repeated, and no injectivity
hypothesis is imposed. Only the nonnegative sequence weights multiply an
inequality. The signed external coefficients are rearranged by exact finite
sum identities. All divisor sums remain over the original primorial; no
transport to a full level interval or analytic density estimate is claimed.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction
open scoped Classical

variable {ι : Type*}

/-- Weighted divisibility count on the original index set. -/
noncomputable def weightedDivCount (I : Finset ι) (a : ι → ℕ)
    (w : ι → ℝ) (d : ℕ) : ℝ :=
  ∑ i ∈ I, if d ∣ a i then w i else 0

/-- Weighted sifted count, with index multiplicity preserved. -/
noncomputable def weightedSequenceSifted (I : Finset ι) (a : ι → ℕ)
    (w : ι → ℝ) (P : Finset ℕ) : ℝ :=
  ∑ i ∈ I, w i * (if (a i).Coprime (P.prod id) then 1 else 0)

/-- The actual external upper family, applied to weighted counts. -/
noncomputable def weightedExternalUpper (P : Finset ℕ) (D ε z : ℝ)
    (I : Finset ι) (a : ι → ℕ) (w : ι → ℝ) : ℝ :=
  ∑ t ∈ externalTags true P D ε z, ∑ d ∈ (P.prod id).divisors,
    externalTerm true P D ε z t d * weightedDivCount I a w d

/-- Singleton specialization of the existing external-family sieve.
This includes the external edge range and the sequence value zero. -/
theorem externalFamily_pointwise_upper (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε z : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hcut : ∀ p ∈ P, (p : ℝ) < z) (n : ℕ) :
    (if n.Coprime (P.prod id) then (1 : ℝ) else 0) ≤
      ∑ t ∈ externalTags true P D ε z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D ε z t d * (if d ∣ n then 1 else 0) := by
  have h := (externalFamily_sequence_sieve P hP hD hε hεsmall hcut
    ({()} : Finset Unit) (fun _ => n) 0 (0 : ArithmeticFunction ℝ)).2
  simpa only [sequenceSifted, externalRemainder, sequenceRemainder,
    sequenceDivisibility, sum_singleton, zero_mul, zero_add, sub_zero] using h

/-- Exact finite reordering; no sign assumptions on either weights or
external coefficients are needed for this identity. -/
theorem weightedExternalUpper_eq_sum_points (P : Finset ℕ) (D ε z : ℝ)
    (I : Finset ι) (a : ι → ℕ) (w : ι → ℝ) :
    weightedExternalUpper P D ε z I a w =
      ∑ i ∈ I, w i *
        (∑ t ∈ externalTags true P D ε z, ∑ d ∈ (P.prod id).divisors,
          externalTerm true P D ε z t d * (if d ∣ a i then 1 else 0)) := by
  unfold weightedExternalUpper weightedDivCount
  simp only [mul_sum]
  rw [sum_comm (s := I)]
  apply sum_congr rfl
  intro t _
  rw [sum_comm (s := I)]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp [mul_comm]

/-- Nonnegative weighted upper sieve for arbitrary indexed natural numbers.
Nonnegativity is required only on the finite index set. -/
theorem externalFamily_weighted_sequence_sieve (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε z : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hcut : ∀ p ∈ P, (p : ℝ) < z)
    (I : Finset ι) (a : ι → ℕ) (w : ι → ℝ) (hw : ∀ i ∈ I, 0 ≤ w i) :
    (∑ i ∈ I, w i * (if (a i).Coprime (P.prod id) then 1 else 0)) ≤
      ∑ t ∈ externalTags true P D ε z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D ε z t d * (∑ i ∈ I, if d ∣ a i then w i else 0) := by
  change weightedSequenceSifted I a w P ≤ weightedExternalUpper P D ε z I a w
  rw [weightedExternalUpper_eq_sum_points]
  exact sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
    (externalFamily_pointwise_upper P hP hD hε hεsmall hcut (a i)) (hw i hi))

/-- Exact centering about an arbitrary function H. This is finite ring
algebra, with no primality, cutoff, positivity, or analytic assumptions. -/
theorem weightedExternalUpper_centering (P : Finset ℕ) (D ε z : ℝ)
    (I : Finset ι) (a : ι → ℕ) (w : ι → ℝ) (H : ℕ → ℝ) :
    weightedExternalUpper P D ε z I a w =
      (∑ t ∈ externalTags true P D ε z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D ε z t d * H d) +
      (∑ t ∈ externalTags true P D ε z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D ε z t d * (weightedDivCount I a w d - H d)) := by
  unfold weightedExternalUpper
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  ring

/-- The weighted sieve with its exact, arbitrarily centered signed error. -/
theorem externalFamily_weighted_sequence_sieve_centered (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε z : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hcut : ∀ p ∈ P, (p : ℝ) < z)
    (I : Finset ι) (a : ι → ℕ) (w : ι → ℝ) (hw : ∀ i ∈ I, 0 ≤ w i)
    (H : ℕ → ℝ) :
    weightedSequenceSifted I a w P ≤
      (∑ t ∈ externalTags true P D ε z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D ε z t d * H d) +
      (∑ t ∈ externalTags true P D ε z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D ε z t d * (weightedDivCount I a w d - H d)) := by
  rw [← weightedExternalUpper_centering]
  exact externalFamily_weighted_sequence_sieve P hP hD hε hεsmall hcut I a w hw

#print axioms weightedDivCount
#print axioms weightedSequenceSifted
#print axioms weightedExternalUpper
#print axioms externalFamily_pointwise_upper
#print axioms weightedExternalUpper_eq_sum_points
#print axioms externalFamily_weighted_sequence_sieve
#print axioms weightedExternalUpper_centering
#print axioms externalFamily_weighted_sequence_sieve_centered

end MathlibNt.SieveTheory.LiLiuPrereqWF
