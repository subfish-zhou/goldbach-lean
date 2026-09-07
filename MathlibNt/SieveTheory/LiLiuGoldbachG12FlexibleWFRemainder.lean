import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWF

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open G12RectangleWF

namespace G12FlexibleWF

def residue (N : ℕ) (A : Finset (ℕ × ℕ)) (d : ℕ) : ℝ :=
  (∑ p ∈ A,
    if d ∣ N-p.2*p.1 then goldbachG12NormalizedCoefficient N p.1 else 0) -
      mass N A / (d.totient : ℝ)

/-- Natural subtraction is only converted on genuinely safe atoms. -/
theorem output_dvd_iff (N d : ℕ) (p : ℕ × ℕ) (hp : p.2*p.1 ≤ N) :
    d ∣ N-p.2*p.1 ↔ Int.ModEq d ((p.1 : ℤ)*p.2) (N : ℤ) := by
  rw [← Nat.modEq_iff_dvd' hp, ← Int.natCast_modEq_iff]
  simp only [Nat.cast_mul, mul_comm]

theorem residue_eq (N : ℕ) (A : Finset (ℕ × ℕ)) (d : ℕ)
    (hsafe : ∀ p ∈ A, p.2*p.1 ≤ N) :
    residue N A d =
      (∑ p ∈ A,
        if Int.ModEq d ((p.1 : ℤ)*p.2) (N : ℤ)
        then goldbachG12NormalizedCoefficient N p.1 else 0) -
          mass N A / (d.totient : ℝ) := by
  unfold residue
  congr 1
  apply sum_congr rfl
  intro p hp
  simp only [output_dvd_iff N d p (hsafe p hp)]

theorem repeated_remainder (N : ℕ) (hEven : Even N) (A : Finset (ℕ × ℕ)) (Z : ℝ)
    {d : ℕ} (hd : d ∣ goldbachB10ProdPrimes N Z) :
    sequenceRemainder (labels N A) (output N) (400 * mass N A)
      AnalyticNumberTheory.Sieve.goldbachNu d = 400 * residue N A d := by
  have hnu : AnalyticNumberTheory.Sieve.goldbachNu d = (1 : ℝ)/d.totient :=
    goldbachB10BoundingSieve_nu_eq_inv_totient (hEven := hEven)
      (ε := 0) (b := 0) (c := 0) (X := 0) hd
  unfold sequenceRemainder sequenceDivisibility
  rw [hnu]
  have ht := labels_test N A (fun p => if d ∣ N-p.2*p.1 then 1 else 0)
  change (∑ a ∈ labels N A, if d ∣ N-a.1.2*a.1.1 then 1 else 0) = _ at ht
  change (∑ a ∈ labels N A, if d ∣ N-a.1.2*a.1.1 then 1 else 0) - _ = _
  rw [ht]
  simp only [mul_ite, mul_one, mul_zero]
  unfold residue
  ring

/-- These are the genuine non-primorial terms introduced by a full-modulus
transport. They cannot be erased merely because the primorial is squarefree. -/
def outsidePrimorial (N : ℕ) (A : Finset (ℕ × ℕ)) (Z Q : ℝ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ (reducedModuli (Ioc 0 ⌊Q⌋₊) (N : ℤ)).filter
    (fun d => ¬ d ∣ goldbachB10ProdPrimes N Z), c d * residue N A d

/-- The actual coefficient is used on the entire original real-level interval. -/
theorem member_full_identity (N : ℕ) (A : Finset (ℕ × ℕ)) (Z Q : ℝ)
    (hsafe : ∀ p ∈ A, p.2*p.1 ≤ N)
    (f : ArithmeticFunction ℝ) (hf : WellFactorable f Q) :
    (∑ d ∈ (goldbachB10ProdPrimes N Z).divisors, f d * residue N A d) =
      common N (A) (Ioc 0 ⌊Q⌋₊) f -
        outsidePrimorial N A Z Q f := by
  have hQ : 0 ≤ Q := (by norm_num : (0 : ℝ) ≤ 1).trans hf.1
  have hsplit := supported_sum_split_primorial hQ hf.2.2.1
    (goldbachB10ProdPrimes_ne_zero N Z)
    (fun d => if Int.gcd (N : ℤ) d = 1 then residue N A d else 0)
  have hg (d : ℕ) (hd : d ∈ (goldbachB10ProdPrimes N Z).divisors) :
      Int.gcd (N : ℤ) d = 1 := by
    have hc := (goldbachB10_dvd_prodPrimes_coprime_N (Nat.dvd_of_mem_divisors hd)).symm
    simpa only [Int.gcd_natCast_natCast] using hc
  have hr : (∑ d ∈ (goldbachB10ProdPrimes N Z).divisors,
      f d * (if Int.gcd (N : ℤ) d = 1 then residue N A d else 0)) =
      ∑ d ∈ (goldbachB10ProdPrimes N Z).divisors, f d * residue N A d := by
    apply sum_congr rfl
    intro d hd
    rw [if_pos (hg d hd)]
  rw [hr] at hsplit
  have hI : Icc 1 ⌊Q⌋₊ = Ioc 0 ⌊Q⌋₊ := by ext d; simp; omega
  rw [hI] at hsplit
  have hfull : (∑ d ∈ Ioc 0 ⌊Q⌋₊,
      f d * (if Int.gcd (N : ℤ) d = 1 then residue N A d else 0)) =
      common N (A) (Ioc 0 ⌊Q⌋₊) f := by
    unfold common reducedModuli
    rw [sum_filter]
    apply sum_congr rfl
    intro d _
    rw [residue_eq N A d hsafe]
    by_cases hd : Int.gcd (N : ℤ) d = 1 <;> simp [hd, mass]
  have hout : (∑ d ∈ (Ioc 0 ⌊Q⌋₊).filter (fun d => ¬ d ∣ goldbachB10ProdPrimes N Z),
      f d * (if Int.gcd (N : ℤ) d = 1 then residue N A d else 0)) =
      outsidePrimorial N A Z Q f := by
    unfold outsidePrimorial reducedModuli
    simp only [sum_filter]
    apply sum_congr rfl
    intro d _
    by_cases h₁ : d ∣ goldbachB10ProdPrimes N Z <;>
      by_cases h₂ : Int.gcd (N : ℤ) d = 1 <;> simp [h₁,h₂]
  rw [hfull, hout] at hsplit
  linarith

/-- Exact decomposition of the real producer remainder: C2 discrepancy,
gcd gate, and the unavoidable signed full-carrier transport correction.
No family member is squarefree-masked and no tuplewise absolute value occurs. -/
theorem external_remainder_decomposition (N : ℕ) (hEven : Even N)
    (A : Finset (ℕ × ℕ)) (Z Q η : ℝ)
    (hsafe : ∀ p ∈ A, p.2*p.1 ≤ N)
    (hfamily : ∀ t ∈ externalTags true (goldbachB10SiftingPrimes N Z)
      (externalInternalLevel Q η) η Z,
      WellFactorable (externalTerm true (goldbachB10SiftingPrimes N Z)
        (externalInternalLevel Q η) η Z t) Q) :
    externalRemainder true (goldbachB10SiftingPrimes N Z)
      (externalInternalLevel Q η) η Z (labels N A) (output N)
        (400 * mass N A) AnalyticNumberTheory.Sieve.goldbachNu =
      400 * ∑ t ∈ externalTags true (goldbachB10SiftingPrimes N Z)
        (externalInternalLevel Q η) η Z,
        let c := externalTerm true (goldbachB10SiftingPrimes N Z)
          (externalInternalLevel Q η) η Z t
        G12LowRectangle.discrepancy N (A) (Ioc 0 ⌊Q⌋₊) c -
          gate N (A) (Ioc 0 ⌊Q⌋₊) c -
          outsidePrimorial N A Z Q c := by
  unfold externalRemainder
  rw [mul_sum]
  apply sum_congr rfl
  intro t ht
  dsimp only
  rw [← common_eq_discrepancy_sub_gate,
    ← member_full_identity N A Z Q hsafe _ (hfamily t ht)]
  rw [mul_sum]
  apply sum_congr rfl
  intro d hd
  rw [repeated_remainder N hEven A Z (Nat.dvd_of_mem_divisors hd)]
  ring

end G12FlexibleWF
