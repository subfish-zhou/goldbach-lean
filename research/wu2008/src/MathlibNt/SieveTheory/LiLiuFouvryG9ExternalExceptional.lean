import MathlibNt.SieveTheory.LiLiuPrereqWFExternalFamily

/-!
# Exceptional mass and finite remainder transport for the actual external family

All coefficients below are the original full-integer `externalTerm` weights.
The upper edge uses a smaller prime carrier only in the existing family definition;
exceptional moduli are still measured against the original primorial. The generic
finite remainder budget does not assume injectivity of any underlying sequence.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction
open scoped Classical

/-- Uniform exceptional mass for each actual upper external member, including
`z > sqrt D`. No primality or cutoff assumption on `P` is needed for this bound. -/
theorem externalUpperTerm_exceptional_mass_le (P : Finset ℕ) {D η : ℝ}
    (z : ℝ) (t : List ℕ) (hD : 2 ≤ D) (hη : 0 < η) (hηsmall : η < 1 / 8)
    (ht : t ∈ externalTags true P D η z) (T : ℕ) :
    (∑ d ∈ (Icc 1 T).filter (fun d => ¬ d ∣ P.prod id),
      |externalTerm true P D η z t d| * (d.totient : ℝ)⁻¹) ≤
        (4 / D ^ (η ^ 2)) * (1 + Real.log T) ^ 2 := by
  by_cases hz : z ≤ Real.sqrt D
  · simp only [externalTags, hz, if_true] at ht
    simpa only [externalTerm, hz, if_true] using
      signedFamilyTerm_exceptional_mass_le true P (geometricSieveLabel D η)
        t hD hη hηsmall ht T
  · simp only [externalTags, hz, if_false, if_true] at ht
    simp only [externalTerm, hz, if_false, if_true]
    have hsub : externalEdgePrimes P D ⊆ P := filter_subset _ _
    have hprod : (externalEdgePrimes P D).prod id ∣ P.prod id :=
      prod_dvd_prod_of_subset _ _ id hsub
    calc
      _ ≤ ∑ d ∈ (Icc 1 T).filter
          (fun d => ¬ d ∣ (externalEdgePrimes P D).prod id),
          |signedFamilyTerm true (externalEdgePrimes P D) D η t d| *
            (d.totient : ℝ)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          exact mem_filter.mpr ⟨(mem_filter.mp hd).1,
            fun hdvd => (mem_filter.mp hd).2 (hdvd.trans hprod)⟩
        · intro d _ _
          positivity
      _ ≤ _ := signedFamilyTerm_exceptional_mass_le true (externalEdgePrimes P D)
        (geometricSieveLabel D η) t hD hη hηsmall ht T

/-- A per-member finite budget for arbitrary real remainders. The majorant is
required only on the finite interval actually used in the sum. -/
theorem externalUpperTerm_exceptional_remainder_le (P : Finset ℕ) {D η : ℝ}
    (z : ℝ) (t : List ℕ) (hD : 2 ≤ D) (hη : 0 < η) (hηsmall : η < 1 / 8)
    (ht : t ∈ externalTags true P D η z) (T : ℕ) (r : ℕ → ℝ)
    (H : ℝ) (hH : 0 ≤ H) (hr : ∀ d ∈ Icc 1 T, |r d| ≤ H / d.totient) :
    |∑ d ∈ (Icc 1 T).filter (fun d => ¬ d ∣ P.prod id),
      externalTerm true P D η z t d * r d| ≤
        H * ((4 / D ^ (η ^ 2)) * (1 + Real.log T) ^ 2) := by
  calc
    _ ≤ ∑ d ∈ (Icc 1 T).filter (fun d => ¬ d ∣ P.prod id),
        |externalTerm true P D η z t d * r d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (Icc 1 T).filter (fun d => ¬ d ∣ P.prod id),
        H * (|externalTerm true P D η z t d| * (d.totient : ℝ)⁻¹) := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul]
      have hb := mul_le_mul_of_nonneg_left (hr d (mem_filter.mp hd).1)
        (abs_nonneg (externalTerm true P D η z t d))
      convert hb using 1
      ring
    _ = H * ∑ d ∈ (Icc 1 T).filter (fun d => ¬ d ∣ P.prod id),
        |externalTerm true P D η z t d| * (d.totient : ℝ)⁻¹ := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (externalUpperTerm_exceptional_mass_le P z t hD hη hηsmall ht T) hH

/-- The sum of absolute per-tag exceptional remainders, with the actual tag
cardinality. This is a finite transport layer, not a G9 endpoint hypothesis. -/
theorem externalUpperFamily_exceptional_remainder_budget (P : Finset ℕ) {D η : ℝ}
    (z : ℝ) (hD : 2 ≤ D) (hη : 0 < η) (hηsmall : η < 1 / 8)
    (T : ℕ) (r : ℕ → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hr : ∀ d ∈ Icc 1 T, |r d| ≤ H / d.totient) :
    (∑ t ∈ externalTags true P D η z,
      |∑ d ∈ (Icc 1 T).filter (fun d => ¬ d ∣ P.prod id),
        externalTerm true P D η z t d * r d|) ≤
      ((externalTags true P D η z).card : ℝ) * H *
        (4 / D ^ (η ^ 2)) * (1 + Real.log T) ^ 2 := by
  calc
    _ ≤ ∑ _t ∈ externalTags true P D η z,
        H * ((4 / D ^ (η ^ 2)) * (1 + Real.log T) ^ 2) :=
      sum_le_sum fun t ht =>
        externalUpperTerm_exceptional_remainder_le P z t hD hη hηsmall ht T r H hH hr
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

/-- Exact primorial-to-full splitting for the same actual member and arbitrary
remainders. Only the summation carrier changes, never the weight. -/
theorem externalTerm_full_sum_split (upper : Bool) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D η : ℝ} (z : ℝ)
    (hD : 2 ≤ D) (hη : 0 < η) (hηsmall : η < 1 / 8)
    (t : List ℕ) (ht : t ∈ externalTags upper P D η z) (r : ℕ → ℝ) :
    (∑ d ∈ Icc 1 ⌊D ^ (1 + η + η ^ 9)⌋₊, externalTerm upper P D η z t d * r d) =
      (∑ d ∈ (P.prod id).divisors, externalTerm upper P D η z t d * r d) +
        ∑ d ∈ (Icc 1 ⌊D ^ (1 + η + η ^ 9)⌋₊).filter (fun d => ¬ d ∣ P.prod id),
          externalTerm upper P D η z t d * r d := by
  have hf := (externalTags_card_and_wellFactorable upper P z hD hη hηsmall).2 t ht
  exact supported_sum_split_primorial (by linarith [hf.1]) hf.2.2.1
    (prod_ne_zero_iff.mpr fun p hp => (hP p hp).ne_zero) r

/-- The exact family identity is obtained by summing memberwise identities;
it makes no well-factorability assertion about an aggregate. -/
theorem externalFamily_full_sum_split (upper : Bool) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D η : ℝ} (z : ℝ)
    (hD : 2 ≤ D) (hη : 0 < η) (hηsmall : η < 1 / 8) (r : ℕ → ℝ) :
    (∑ t ∈ externalTags upper P D η z,
      ∑ d ∈ Icc 1 ⌊D ^ (1 + η + η ^ 9)⌋₊, externalTerm upper P D η z t d * r d) =
      (∑ t ∈ externalTags upper P D η z,
        ∑ d ∈ (P.prod id).divisors, externalTerm upper P D η z t d * r d) +
      ∑ t ∈ externalTags upper P D η z,
        ∑ d ∈ (Icc 1 ⌊D ^ (1 + η + η ^ 9)⌋₊).filter (fun d => ¬ d ∣ P.prod id),
          externalTerm upper P D η z t d * r d := by
  rw [← sum_add_distrib]
  exact sum_congr rfl fun t ht =>
    externalTerm_full_sum_split upper P hP z hD hη hηsmall t ht r

/-- Quantitative primorial-to-full transport, retaining absolute values
memberwise. The generic remainder majorant is local to `Icc 1 (floor Q)`. -/
theorem externalUpperFamily_full_transport_budget (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D η : ℝ} (z : ℝ)
    (hD : 2 ≤ D) (hη : 0 < η) (hηsmall : η < 1 / 8)
    (r : ℕ → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hr : ∀ d ∈ Icc 1 ⌊D ^ (1 + η + η ^ 9)⌋₊, |r d| ≤ H / d.totient) :
    (∑ t ∈ externalTags true P D η z,
      |(∑ d ∈ Icc 1 ⌊D ^ (1 + η + η ^ 9)⌋₊, externalTerm true P D η z t d * r d) -
        ∑ d ∈ (P.prod id).divisors, externalTerm true P D η z t d * r d|) ≤
      ((externalTags true P D η z).card : ℝ) * H * (4 / D ^ (η ^ 2)) *
        (1 + Real.log (⌊D ^ (1 + η + η ^ 9)⌋₊ : ℕ)) ^ 2 := by
  calc
    _ = ∑ t ∈ externalTags true P D η z,
        |∑ d ∈ (Icc 1 ⌊D ^ (1 + η + η ^ 9)⌋₊).filter (fun d => ¬ d ∣ P.prod id),
          externalTerm true P D η z t d * r d| := by
      apply sum_congr rfl
      intro t ht
      rw [externalTerm_full_sum_split true P hP z hD hη hηsmall t ht r,
        add_sub_cancel_left]
    _ ≤ _ := externalUpperFamily_exceptional_remainder_budget P z hD hη hηsmall
      _ r H hH hr

#print axioms externalUpperFamily_full_transport_budget
#print axioms externalUpperTerm_exceptional_mass_le
#print axioms externalUpperTerm_exceptional_remainder_le
#print axioms externalUpperFamily_exceptional_remainder_budget
#print axioms externalTerm_full_sum_split
#print axioms externalFamily_full_sum_split

end MathlibNt.SieveTheory.LiLiuPrereqWF
