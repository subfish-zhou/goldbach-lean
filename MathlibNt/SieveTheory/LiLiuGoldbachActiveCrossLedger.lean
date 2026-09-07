import MathlibNt.SieveTheory.LiLiuGoldbachCrossProductLedger
import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindowAP
import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedDistribution

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The literal cross count is supported on the proved balanced family.
The output-prime condition stays in the counted fibre, never in the coefficient. -/
theorem goldbachWeight_activeCrossLedger (ρ δ : ℝ) (hρ : 0 < ρ)
    (hρK : ρ < 53/(2*Real.exp Real.eulerMascheroniConstant)) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ((53/(2*Real.exp Real.eulerMascheroniConstant)-ρ) *
          (goldbachPairIdealSum N (2*ρ)
            (goldbachG6Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))) +
           goldbachPairIdealSum N (2*ρ)
            (goldbachG7Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
              ((N : ℝ)^(3/11 : ℝ)))) +
          (124341093/200000000 : ℝ) - goldbachB9PaperSplitIntegral -
          10385101/100000000 - δ) *
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) -
          (400 * ∑ m ∈ goldbachG12ActiveProductSupport N,
            goldbachG12NormalizedCoefficient N m *
              ((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).card : ℝ)) ≤ 4*(D19 N : ℝ) := by
  obtain ⟨ε₀,hε₀,hε₀u,hm⟩ := goldbachWeight_crossProductLedger ρ δ hρ hρK hδ
  refine ⟨ε₀,hε₀,hε₀u,?_⟩
  intro ε hε hεlt
  obtain ⟨N₀,hN₀,hn⟩ := hm ε hε hεlt
  refine ⟨N₀,hN₀,?_⟩
  intro N hN hEven
  have h := hn N hN hEven
  rw [goldbachG12ProductPrimeTotal_eq_active N ε (by omega)] at h
  exact h

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
