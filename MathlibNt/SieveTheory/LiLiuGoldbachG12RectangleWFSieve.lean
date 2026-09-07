import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWF
import MathlibNt.SieveTheory.LiLiuGoldbachG12OutputEnvelope

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace G12RectangleWF

/-- Pointwise conversion to the producer's omega convention. -/
def omegaDensity : ArithmeticFunction ℝ :=
  ⟨fun d => (d : ℝ) * AnalyticNumberTheory.Sieve.goldbachNu d, by simp⟩

theorem omegaDensity_mult : omegaDensity.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · change ((1 : ℕ) : ℝ) * AnalyticNumberTheory.Sieve.goldbachNu 1 = 1
    simp [AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative.map_one]
  · intro m n hmn
    change ((m*n : ℕ) : ℝ) * AnalyticNumberTheory.Sieve.goldbachNu (m*n) = _
    rw [AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative.map_mul_of_coprime hmn]
    simp only [Nat.cast_mul]
    change _ = ((m : ℝ) * AnalyticNumberTheory.Sieve.goldbachNu m) *
      ((n : ℝ) * AnalyticNumberTheory.Sieve.goldbachNu n)
    ring

theorem density_eq : primeDensity omegaDensity = AnalyticNumberTheory.Sieve.goldbachNu := by
  ext d
  by_cases hd : d = 0
  · subst d; simp
  · change (d : ℝ) * AnalyticNumberTheory.Sieve.goldbachNu d / d = _
    field_simp

theorem local_density_bounds (N : ℕ) (hEven : Even N) (Z : ℝ) :
    ∀ p ∈ goldbachB10SiftingPrimes N Z,
      0 ≤ omegaDensity p / (p : ℝ) ∧ omegaDensity p / (p : ℝ) < 1 := by
  intro p hp
  have hprime := (mem_goldbachB10SiftingPrimes_iff.mp hp).2.1
  have hd : p ∣ goldbachB10ProdPrimes N Z := dvd_prod_of_mem id hp
  change 0 ≤ primeDensity omegaDensity p ∧ primeDensity omegaDensity p < 1
  rw [density_eq]
  exact ⟨(goldbachB10BoundingSieve N hEven 0 0 0 Z 0).nu_pos_of_prime p hprime hd |>.le,
    (goldbachB10BoundingSieve N hEven 0 0 0 Z 0).nu_lt_one_of_prime p hprime hd⟩

/-- One inherited B10 constant, uniform before every rectangle parameter. -/
theorem exists_local_dimension : ∃ K : ℝ, 1 < K ∧
    ∀ (N : ℕ) (_hEven : Even N) (Z : ℝ),
      DimensionOneProductBound (goldbachB10SiftingPrimes N Z) (primeDensity omegaDensity) K := by
  obtain ⟨K,hK,h⟩ := exists_goldbachB10BoundingSieve_dimensionOneLocalProductBound
  refine ⟨K,hK,?_⟩
  intro N hEven Z w z hw hwz
  have hb := h N hEven 0 0 0 Z 0 w z hw hwz.le
  rw [density_eq]
  have hf : (goldbachB10SiftingPrimes N Z).filter
      (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) =
      (goldbachB10SiftingPrimes N Z).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z) := by
    ext p
    simp only [mem_filter]
    exact ⟨fun hp => ⟨hp.1,hp.2.2⟩,
      fun hp => ⟨hp.1,(mem_goldbachB10SiftingPrimes_iff.mp hp.1).2.1,hp.2⟩⟩
  rw [hf]
  simpa only [goldbachB10BoundingSieve, goldbachB10ProdPrimes_primeFactors] using hb

def smallOutput (N : ℕ) (ε Z : ℝ) (M T : ℕ) : ℝ :=
  ∑ a ∈ labels N ε M T, if output N a < Nat.ceil Z then 1 else 0

def primeCount (N : ℕ) (ε : ℝ) (M T : ℕ) : ℝ :=
  ∑ a ∈ labels N ε M T, if (output N a).Prime then 1 else 0

theorem primeCount_eq_original (N : ℕ) (ε : ℝ) (M T : ℕ) :
    primeCount N ε M T = 400 * ∑ p ∈ G12LowRectangle.rectangle N ε M T,
      goldbachG12NormalizedCoefficient N p.1 * (if (N-p.2*p.1).Prime then 1 else 0) :=
  labels_test N ε M T (fun p => if (N-p.2*p.1).Prime then 1 else 0)

theorem prime_le_sifted_small (N : ℕ) (ε Z : ℝ) (M T : ℕ) :
    primeCount N ε M T ≤
      sequenceSifted (labels N ε M T) (output N) (goldbachB10SiftingPrimes N Z) +
        smallOutput N ε Z M T := by
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

/-- The genuine producer is called on the actual repeated rectangle labels.
The remainder is the signed sum of exactly the displayed family members. -/
theorem exists_rectangle_sieve :
    ∃ K C : ℝ, 1 < K ∧ 0 < C ∧ ∀ η : ℝ, 0 < η → η < 1/8 →
      ∃ Q₀ : ℝ, 4 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
        ∀ (N : ℕ) (_hEven : Even N) (ε Z : ℝ) (M T : ℕ),
          2 ≤ Z → Z ≤ Real.sqrt Q →
          let P := goldbachB10SiftingPrimes N Z
          let D := externalInternalLevel Q η
          let V := ∏ p ∈ P, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)
          let E := C * (η + (η^8)⁻¹ * Real.exp (6*K+2) * Real.log Q^(-(1/3 : ℝ)))
          (∀ t ∈ externalTags true P D η Z,
            WellFactorable (externalTerm true P D η Z t) Q) ∧
          primeCount N ε M T ≤ 400 * mass N ε M T * V *
            (jr1965F (Real.log Q / Real.log Z) + E) +
            externalRemainder true P D η Z (labels N ε M T) (output N)
              (400 * mass N ε M T) AnalyticNumberTheory.Sieve.goldbachNu +
            smallOutput N ε Z M T := by
  obtain ⟨K,hK,hlocal⟩ := exists_local_dimension
  obtain ⟨C,hC,hproducer⟩ := exists_external_sieve_common_family (ι := Atom)
  refine ⟨K,C,hK,hC,?_⟩
  intro η hη hηu
  obtain ⟨Q₀,hQ₀,hproducer⟩ := hproducer η hη hηu
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQ N hEven ε Z M T hZ hZQ
  have hh := hproducer Q hQ (goldbachB10SiftingPrimes N Z)
    (fun p hp => (mem_goldbachB10SiftingPrimes_iff.mp hp).2.1)
    omegaDensity omegaDensity_mult (local_density_bounds N hEven Z)
    Z hZ hZQ (fun p hp => Nat.lt_ceil.mp (mem_goldbachB10SiftingPrimes_iff.mp hp).1)
    K (by linarith) (hlocal N hEven Z)
  dsimp only at hh ⊢
  refine ⟨(hh.1 true).2,?_⟩
  have hX : 0 ≤ 400 * mass N ε M T := by rw [← labels_card]; positivity
  have hu := (hh.2 (labels N ε M T) (output N) (400 * mass N ε M T) hX).2
  have hd (p : ℕ) : omegaDensity p / (p : ℝ) = AnalyticNumberTheory.Sieve.goldbachNu p :=
    congrArg (fun f : ArithmeticFunction ℝ => f p) density_eq
  simp only [density_eq, hd] at hu
  exact (prime_le_sifted_small N ε Z M T).trans (add_le_add hu le_rfl)

end G12RectangleWF
