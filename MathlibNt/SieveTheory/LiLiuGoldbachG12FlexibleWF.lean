import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFSmall
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleRectangleC2

noncomputable section
open Classical Finset G12RectangleWF
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace G12FlexibleWF

/-- Actual repeated labels, not a replacement of the normalized weight by one. -/
def labels (N : ℕ) (A : Finset (ℕ × ℕ)) : Finset Atom :=
  ((A).sigma
    (fun p => range (G12RectangleWF.multiplicity N p.1))).image (fun p => (p.1,p.2))

def mass (N : ℕ) (A : Finset (ℕ × ℕ)) : ℝ :=
  ∑ p ∈ A, goldbachG12NormalizedCoefficient N p.1

/-- Every test retains precisely the original factor 400. -/
theorem labels_test (N : ℕ) (A : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℝ) :
    (∑ a ∈ labels N A, f a.1) =
      400 * ∑ p ∈ A,
        goldbachG12NormalizedCoefficient N p.1 * f p := by
  rw [G12LowRectangle.restore_multiplicity]
  unfold labels
  rw [sum_image]
  · rw [sum_sigma]
    simp [G12RectangleWF.multiplicity, mul_comm]
  · intro a _ b _ hab
    cases a
    cases b
    obtain ⟨h₁,h₂⟩ := Prod.mk.inj hab
    cases h₁
    cases h₂
    rfl

theorem labels_card (N : ℕ) (A : Finset (ℕ × ℕ)) :
    ((labels N A).card : ℝ) = 400 * mass N A := by
  simpa [mass] using labels_test N A (fun _ => 1)

def smallOutput (N : ℕ) (A : Finset (ℕ × ℕ)) (Z : ℝ) : ℝ :=
  ∑ a ∈ labels N A, if output N a < Nat.ceil Z then 1 else 0

def primeCount (N : ℕ) (A : Finset (ℕ × ℕ)) : ℝ :=
  ∑ a ∈ labels N A, if (output N a).Prime then 1 else 0

theorem primeCount_eq_original (N : ℕ) (A : Finset (ℕ × ℕ)) :
    primeCount N A = 400 * ∑ p ∈ A,
      goldbachG12NormalizedCoefficient N p.1 * (if (N-p.2*p.1).Prime then 1 else 0) :=
  labels_test N A (fun p => if (N-p.2*p.1).Prime then 1 else 0)

theorem prime_le_sifted_small (N : ℕ) (A : Finset (ℕ × ℕ)) (Z : ℝ) :
    primeCount N A ≤
      sequenceSifted (labels N A) (output N) (goldbachB10SiftingPrimes N Z) +
        smallOutput N A Z := by
  unfold primeCount sequenceSifted smallOutput
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro a _
  by_cases hp : (output N a).Prime
  · rw [if_pos hp]
    by_cases hc : (output N a).Coprime (goldbachB10ProdPrimes N Z)
    · change _ ≤ (if (output N a).Coprime (goldbachB10ProdPrimes N Z) then 1 else 0) + _
      rw [if_pos hc]
      split_ifs <;> norm_num
    · have hd := (hp.coprime_iff_not_dvd).not.mp hc
      have hd' : output N a ∣ goldbachB10ProdPrimes N Z := by simpa using hd
      have hs := Nat.lt_ceil.mpr (prime_dvd_goldbachB10ProdPrimes_lt hp hd')
      change _ ≤ (if (output N a).Coprime (goldbachB10ProdPrimes N Z) then 1 else 0) + _
      simp [hc, hs]
  · rw [if_neg hp]
    split_ifs <;> norm_num

/-- The genuine producer is called on the actual repeated labels on any finite atom set.
The remainder is the signed sum of exactly the displayed family members. -/
theorem exists_atom_sieve :
    ∃ K C : ℝ, 1 < K ∧ 0 < C ∧ ∀ η : ℝ, 0 < η → η < 1/8 →
      ∃ Q₀ : ℝ, 4 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
        ∀ (N : ℕ) (_hEven : Even N) (A : Finset (ℕ × ℕ)) (Z : ℝ),
          2 ≤ Z → Z ≤ Real.sqrt Q →
          let P := goldbachB10SiftingPrimes N Z
          let D := externalInternalLevel Q η
          let V := ∏ p ∈ P, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)
          let E := C * (η + (η^8)⁻¹ * Real.exp (6*K+2) * Real.log Q^(-(1/3 : ℝ)))
          (∀ t ∈ externalTags true P D η Z,
            WellFactorable (externalTerm true P D η Z t) Q) ∧
          primeCount N A ≤ 400 * mass N A * V *
            (jr1965F (Real.log Q / Real.log Z) + E) +
            externalRemainder true P D η Z (labels N A) (output N)
              (400 * mass N A) AnalyticNumberTheory.Sieve.goldbachNu +
            smallOutput N A Z := by
  obtain ⟨K,hK,hlocal⟩ := exists_local_dimension
  obtain ⟨C,hC,hproducer⟩ := exists_external_sieve_common_family (ι := Atom)
  refine ⟨K,C,hK,hC,?_⟩
  intro η hη hηu
  obtain ⟨Q₀,hQ₀,hproducer⟩ := hproducer η hη hηu
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQ N hEven A Z hZ hZQ
  have hh := hproducer Q hQ (goldbachB10SiftingPrimes N Z)
    (fun p hp => (mem_goldbachB10SiftingPrimes_iff.mp hp).2.1)
    omegaDensity omegaDensity_mult (local_density_bounds N hEven Z)
    Z hZ hZQ (fun p hp => Nat.lt_ceil.mp (mem_goldbachB10SiftingPrimes_iff.mp hp).1)
    K (by linarith) (hlocal N hEven Z)
  dsimp only at hh ⊢
  refine ⟨(hh.1 true).2,?_⟩
  have hX : 0 ≤ 400 * mass N A := by rw [← labels_card]; positivity
  have hu := (hh.2 (labels N A) (output N) (400 * mass N A) hX).2
  have hd (p : ℕ) : omegaDensity p / (p : ℝ) = AnalyticNumberTheory.Sieve.goldbachNu p :=
    congrArg (fun f : ArithmeticFunction ℝ => f p) density_eq
  simp only [density_eq, hd] at hu
  exact (prime_le_sifted_small N A Z).trans (add_le_add hu le_rfl)

end G12FlexibleWF
