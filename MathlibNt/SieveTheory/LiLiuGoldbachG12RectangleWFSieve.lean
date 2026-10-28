import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWF
import MathlibNt.SieveTheory.LiLiuGoldbachG12RosserFactor


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


end G12RectangleWF
