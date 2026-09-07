import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpOutputIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachPairIntegralLedger
import MathlibNt.SieveTheory.LiLiuGoldbachG12IntegralReduction

noncomputable section
open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Fixed author-weighted G12 ledger. The full actual JR positive constant is
retained; this does not assert a rational numerical estimate or net positivity. -/
theorem goldbachWeight_sharpCrossIntegralLedger (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (goldbachG67IntegralConstant + (124341093/200000000 : ℝ) -
          goldbachB9PaperSplitIntegral - 10385101/100000000 -
          goldbachG12SharpIntegralConstant - δ)*
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
          4*(D19 N : ℝ) := by
  obtain ⟨ε₀,he0,heu,hold⟩ := goldbachWeight_pairIntegralLedger (δ/2) (half_pos hδ)
  refine ⟨ε₀,he0,heu,?_⟩
  intro ε he helt
  obtain ⟨L,hL,hl⟩ := hold ε he helt
  obtain ⟨M,_,hm⟩ := G12SharpOutput.original_total_integral (δ/2) (half_pos hδ) ε he
    (helt.le.trans heu)
  refine ⟨max L M,by omega,?_⟩
  intro N hN hEven
  have hp := hl N (by omega) hEven
  have hu := hm N (by omega) hEven
  rw [goldbachG12ProductPrimeTotal_eq_active N ε (by omega)] at hu
  linarith only [hp,hu]


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
