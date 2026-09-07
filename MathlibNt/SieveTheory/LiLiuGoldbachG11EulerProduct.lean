import MathlibNt.SieveTheory.LiLiuGoldbachG11BoundingSieve
import MathlibNt.SieveTheory.LiLiuGoldbachB10SieveProduct

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

theorem goldbachG11Linked_sieveProduct_eq (N : ℕ) (hEven : Even N) (ε Z X : ℝ) :
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
      (goldbachG11LinkedBoundingSieve N hEven ε Z X) = goldbachB10PrimeProduct N Z :=
  (goldbachB10PrimeProduct_eq_sieveProductPrimeFactors N hEven 0 0 0 Z X).symm

/-- The already proved uniform Euler comparison on the actual G11 sieve. -/
theorem goldbachG11Linked_sieveProduct_log_le (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ (N : ℕ), 4 ≤ N → ∀ hEven : Even N,
      ∀ ε X Z : ℝ, Z₀ ≤ Z →
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (goldbachG11LinkedBoundingSieve N hEven ε Z X) * Real.log Z ≤
      2 * Real.exp (-Real.eulerMascheroniConstant) * (1+η) * SingularSeries.liuSingularSeries N := by
  obtain ⟨Z₀,hZ₀,hprod⟩ := goldbachB10BoundingSieve_sieveProductPrimeFactors_log_le_liuSingularSeries η hη
  exact ⟨Z₀,hZ₀,fun N hN hEven _ε X Z hZ => hprod N hN hEven 0 0 0 X Z hZ⟩

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig