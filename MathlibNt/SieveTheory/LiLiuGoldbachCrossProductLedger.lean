import MathlibNt.SieveTheory.LiLiuGoldbachG12CrossProductPaid
import MathlibNt.SieveTheory.LiLiuGoldbachIdealKernelLedger

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The original weight ledger now uses the exact good cross product count.
The additional bad-body loss is separately paid, not reused for free. -/
theorem goldbachWeight_crossProductLedger (ρ δ : ℝ) (hρ : 0 < ρ)
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
          (goldbachG12ProductPrimeTotal N ε ((N : ℝ)^(4/53 : ℝ))
            ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ) ≤ 4*(D19 N : ℝ) := by
  obtain ⟨ε₀,hε₀,hε₀u,hm⟩ := goldbachWeight_idealKernelLedger ρ (δ/2) hρ hρK (by positivity)
  obtain ⟨Nb,_,hb⟩ := goldbachG12_roughSum_le_productPrime_normalized (δ/2) (by positivity)
  refine ⟨ε₀,hε₀,hε₀u,?_⟩
  intro ε hε hεlt
  obtain ⟨Nm,hNm,hn⟩ := hm ε hε hεlt
  refine ⟨max Nm Nb,by omega,?_⟩
  intro N hN hEven
  have hmain := hn N (by omega) hEven
  have hbad := hb N (by omega) ε hε.le ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ))
  nlinarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
