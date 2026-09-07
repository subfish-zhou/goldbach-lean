import MathlibNt.SieveTheory.LiLiuGoldbachG12NormalizedIntegralBound
import MathlibNt.SieveTheory.LiLiuGoldbachPairIntegralLedger

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A fixed integral ledger after the actual G12 output sieve and cross quadrature.
The uniform-level upper integral is retained literally; no final positive margin is asserted. -/
theorem goldbachWeight_uniformCrossIntegralLedger (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (goldbachG67IntegralConstant + (124341093/200000000 : ℝ) -
          goldbachB9PaperSplitIntegral - 10385101/100000000 -
          8*(564383/1000000 : ℝ)*goldbachG12PrimeIntegral (fun _ => 1) - δ) *
          (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
          4*(D19 N : ℝ) := by
  obtain ⟨ε₀,hε₀,hε₀u,hledger⟩ := goldbachWeight_pairIntegralLedger (δ/2) (half_pos hδ)
  obtain ⟨M,_,hupper⟩ := goldbachG12OutputTotal_le_uniformIntegral (δ/2) (half_pos hδ)
  refine ⟨ε₀,hε₀,hε₀u,?_⟩
  intro ε hε hεlt
  obtain ⟨L,hL,hl⟩ := hledger ε hε hεlt
  refine ⟨max L M,by omega,?_⟩
  intro N hN hEven
  have hp := hl N (by omega) hEven
  have hu := hupper N (by omega) hEven ε
  linarith only [hp,hu]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
