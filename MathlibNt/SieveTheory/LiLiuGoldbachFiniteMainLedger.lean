import MathlibNt.SieveTheory.LiLiuGoldbachG67NormalizedLower
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughConsumed

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual weight ledger after G6/G7 BV payment and G12 exception payment.
Its two positive terms are the original finite signed Rosser main sums; its
negative term is the original cross rough count. No integral estimate is assumed. -/
theorem goldbachWeight_finiteMainLedger :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
            goldbachPairLowerMain N ε B
              (goldbachG6Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))) +
            goldbachPairLowerMain N ε B
              (goldbachG7Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
                ((N : ℝ)^(3/11 : ℝ))) -
            ((∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
                ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
              goldbachG11RoughCount N ε v : ℤ) : ℝ) +
            ((124341093/200000000 : ℝ) - goldbachB9PaperSplitIntegral -
              10385101/100000000 - δ) *
              (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
            4 * (D19 N : ℝ) := by
  obtain ⟨B, hB, hp⟩ := goldbachG67_lowerRosser_normalized
  refine ⟨B, hB, ?_⟩
  intro δ hδ
  have hthird : 0 < δ/3 := by positivity
  obtain ⟨ε₀, hε₀, hε₀u, hm⟩ :=
    goldbachWeight_G12Rough_allRetained_small_epsilon (δ/3) hthird
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Np, hNp, hn⟩ := hp (δ/3) hthird ε hε (hεlt.trans_le hε₀u)
  obtain ⟨Nm, _, hnmain⟩ := hm ε hε hεlt
  refine ⟨max Np Nm, by omega, ?_⟩
  intro N hN hEven
  obtain ⟨h6, h7⟩ := hn N (by omega) hEven
  have hmain := hnmain N (by omega) hEven
  push_cast at hmain ⊢
  nlinarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
