import MathlibNt.SieveTheory.LiLiuGoldbachG67IdealNormalization
import MathlibNt.SieveTheory.LiLiuGoldbachMovingKernelLedger

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual weight ledger with ideal-coordinate, scalar-normalized pair sums.
The sieve level and its logarithmic shrink no longer appear in the conclusion.
The finite pair sums and original cross rough sum are not yet replaced by integrals. -/
theorem goldbachWeight_idealKernelLedger (ρ δ : ℝ) (hρ : 0 < ρ)
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
          ((∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
              ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
            goldbachG11RoughCount N ε v : ℤ) : ℝ) ≤ 4*(D19 N : ℝ) := by
  obtain ⟨B, hB, hm⟩ := goldbachWeight_movingKernelLedger
  obtain ⟨εm, hεm, hεmu, hmain⟩ := hm ρ hρ δ hδ
  obtain ⟨εn, hεn, _, hnorm⟩ := goldbachG67_ideal_normalized B ρ hB hρ hρK
  refine ⟨min εm εn, lt_min hεm hεn, (min_le_left _ _).trans hεmu, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nm, hNm, hmN⟩ := hmain ε hε (hεlt.trans_le (min_le_left _ _))
  obtain ⟨Nn, _, hnN⟩ := hnorm ε hε (hεlt.trans_le (min_le_right _ _))
  refine ⟨max Nm Nn, by omega, ?_⟩
  intro N hN hEven
  have hmain := hmN N (by omega) hEven
  obtain ⟨h6, h7⟩ := hnN N (by omega) hEven
  nlinarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
