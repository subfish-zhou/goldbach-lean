import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFSieve

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace G12RectangleWF

def residue (N : ℕ) (ε : ℝ) (M T d : ℕ) : ℝ :=
  (∑ p ∈ G12LowRectangle.rectangle N ε M T,
    if d ∣ N-p.2*p.1 then goldbachG12NormalizedCoefficient N p.1 else 0) -
      mass N ε M T / (d.totient : ℝ)

theorem output_dvd_iff (N : ℕ) (ε : ℝ) (M T d : ℕ)
    (p : ℕ × ℕ) (hp : p ∈ G12LowRectangle.rectangle N ε M T) :
    d ∣ N-p.2*p.1 ↔ Int.ModEq d ((p.1 : ℤ)*p.2) (N : ℤ) := by
  obtain ⟨hm,hr⟩ := mem_product.mp hp
  have hn := (mem_filter.mp hm).2.2.2.2
  have hrT := (mem_Ioc.mp (mem_filter.mp hr).1).2
  have hprod : p.2*p.1 ≤ N := ((Nat.mul_le_mul_right p.1 hrT).trans_lt hn).le
  rw [← Nat.modEq_iff_dvd' hprod, ← Int.natCast_modEq_iff]
  simp only [Nat.cast_mul, mul_comm]

theorem residue_eq (N : ℕ) (ε : ℝ) (M T d : ℕ) :
    residue N ε M T d =
      (∑ p ∈ G12LowRectangle.rectangle N ε M T,
        if Int.ModEq d ((p.1 : ℤ)*p.2) (N : ℤ)
        then goldbachG12NormalizedCoefficient N p.1 else 0) -
          mass N ε M T / (d.totient : ℝ) := by
  unfold residue
  congr 1
  apply sum_congr rfl
  intro p hp
  simp only [output_dvd_iff N ε M T d p hp]

theorem repeated_remainder (N : ℕ) (hEven : Even N) (ε Z : ℝ) (M T : ℕ)
    {d : ℕ} (hd : d ∣ goldbachB10ProdPrimes N Z) :
    sequenceRemainder (labels N ε M T) (output N) (400 * mass N ε M T)
      AnalyticNumberTheory.Sieve.goldbachNu d = 400 * residue N ε M T d := by
  have hnu : AnalyticNumberTheory.Sieve.goldbachNu d = (1 : ℝ)/d.totient :=
    goldbachB10BoundingSieve_nu_eq_inv_totient (hEven := hEven)
      (ε := 0) (b := 0) (c := 0) (X := 0) hd
  unfold sequenceRemainder sequenceDivisibility
  rw [hnu]
  have ht := labels_test N ε M T (fun p => if d ∣ N-p.2*p.1 then 1 else 0)
  change (∑ a ∈ labels N ε M T, if d ∣ N-a.1.2*a.1.1 then 1 else 0) = _ at ht
  change (∑ a ∈ labels N ε M T, if d ∣ N-a.1.2*a.1.1 then 1 else 0) - _ = _
  rw [ht]
  simp only [mul_ite, mul_one, mul_zero]
  unfold residue
  ring

/-- These are the genuine non-primorial terms introduced by a full-modulus
transport. They cannot be erased merely because the primorial is squarefree. -/
def outsidePrimorial (N : ℕ) (ε Z Q : ℝ) (M T : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ (reducedModuli (Ioc 0 ⌊Q⌋₊) (N : ℤ)).filter
    (fun d => ¬ d ∣ goldbachB10ProdPrimes N Z), c d * residue N ε M T d

/-- The actual coefficient is used on the entire original real-level interval. -/
theorem member_full_identity (N : ℕ) (ε Z Q : ℝ) (M T : ℕ)
    (f : ArithmeticFunction ℝ) (hf : WellFactorable f Q) :
    (∑ d ∈ (goldbachB10ProdPrimes N Z).divisors, f d * residue N ε M T d) =
      common N (G12LowRectangle.rectangle N ε M T) (Ioc 0 ⌊Q⌋₊) f -
        outsidePrimorial N ε Z Q M T f := by
  have hQ : 0 ≤ Q := (by norm_num : (0 : ℝ) ≤ 1).trans hf.1
  have hsplit := supported_sum_split_primorial hQ hf.2.2.1
    (goldbachB10ProdPrimes_ne_zero N Z)
    (fun d => if Int.gcd (N : ℤ) d = 1 then residue N ε M T d else 0)
  have hg (d : ℕ) (hd : d ∈ (goldbachB10ProdPrimes N Z).divisors) :
      Int.gcd (N : ℤ) d = 1 := by
    have hc := (goldbachB10_dvd_prodPrimes_coprime_N (Nat.dvd_of_mem_divisors hd)).symm
    simpa only [Int.gcd_natCast_natCast] using hc
  have hr : (∑ d ∈ (goldbachB10ProdPrimes N Z).divisors,
      f d * (if Int.gcd (N : ℤ) d = 1 then residue N ε M T d else 0)) =
      ∑ d ∈ (goldbachB10ProdPrimes N Z).divisors, f d * residue N ε M T d := by
    apply sum_congr rfl
    intro d hd
    rw [if_pos (hg d hd)]
  rw [hr] at hsplit
  have hI : Icc 1 ⌊Q⌋₊ = Ioc 0 ⌊Q⌋₊ := by ext d; simp; omega
  rw [hI] at hsplit
  have hfull : (∑ d ∈ Ioc 0 ⌊Q⌋₊,
      f d * (if Int.gcd (N : ℤ) d = 1 then residue N ε M T d else 0)) =
      common N (G12LowRectangle.rectangle N ε M T) (Ioc 0 ⌊Q⌋₊) f := by
    unfold common reducedModuli
    rw [sum_filter]
    apply sum_congr rfl
    intro d _
    rw [residue_eq]
    by_cases hd : Int.gcd (N : ℤ) d = 1 <;> simp [hd, mass]
  have hout : (∑ d ∈ (Ioc 0 ⌊Q⌋₊).filter (fun d => ¬ d ∣ goldbachB10ProdPrimes N Z),
      f d * (if Int.gcd (N : ℤ) d = 1 then residue N ε M T d else 0)) =
      outsidePrimorial N ε Z Q M T f := by
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
    (ε Z Q η : ℝ) (M T : ℕ)
    (hfamily : ∀ t ∈ externalTags true (goldbachB10SiftingPrimes N Z)
      (externalInternalLevel Q η) η Z,
      WellFactorable (externalTerm true (goldbachB10SiftingPrimes N Z)
        (externalInternalLevel Q η) η Z t) Q) :
    externalRemainder true (goldbachB10SiftingPrimes N Z)
      (externalInternalLevel Q η) η Z (labels N ε M T) (output N)
        (400 * mass N ε M T) AnalyticNumberTheory.Sieve.goldbachNu =
      400 * ∑ t ∈ externalTags true (goldbachB10SiftingPrimes N Z)
        (externalInternalLevel Q η) η Z,
        let c := externalTerm true (goldbachB10SiftingPrimes N Z)
          (externalInternalLevel Q η) η Z t
        G12LowRectangle.discrepancy N (G12LowRectangle.rectangle N ε M T) (Ioc 0 ⌊Q⌋₊) c -
          gate N (G12LowRectangle.rectangle N ε M T) (Ioc 0 ⌊Q⌋₊) c -
          outsidePrimorial N ε Z Q M T c := by
  unfold externalRemainder
  rw [mul_sum]
  apply sum_congr rfl
  intro t ht
  dsimp only
  rw [← common_eq_discrepancy_sub_gate,
    ← member_full_identity N ε Z Q M T _ (hfamily t ht)]
  rw [mul_sum]
  apply sum_congr rfl
  intro d hd
  rw [repeated_remainder N hEven ε Z M T (Nat.dvd_of_mem_divisors hd)]
  ring

/-- The very same full function is admissible for C2, without a mask. -/
theorem member_signedWF (Q : ℝ) (f : ArithmeticFunction ℝ) (hf : WellFactorable f Q) :
    SignedWellFactorable 1 Q (fun d => f d) := wellFactorable_to_signed hf

end G12RectangleWF
