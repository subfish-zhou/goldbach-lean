import MathlibNt.SieveTheory.LiLiuGoldbachG67MovingLower
import MathlibNt.SieveTheory.LiLiuGoldbachG67NormalizedLower
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughConsumed

open scoped BigOperators
open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Actual moving JR kernels in the strongest weight ledger. The independent
positive parameter rho is the density tolerance; delta pays all additive errors. -/
theorem goldbachWeight_movingKernelLedger :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : ℝ, 0 < ρ → ∀ δ : ℝ, 0 < δ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
            goldbachPairMovingMain N hEven ε B ρ
              (goldbachG6Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))) +
            goldbachPairMovingMain N hEven ε B ρ
              (goldbachG7Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
                ((N : ℝ)^(3/11 : ℝ))) -
            ((∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
                ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
              goldbachG11RoughCount N ε v : ℤ) : ℝ) +
            ((124341093/200000000 : ℝ) - goldbachB9PaperSplitIntegral -
              10385101/100000000 - δ) *
              (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
            4 * (D19 N : ℝ) := by
  obtain ⟨B, hB, C, _, hp⟩ := goldbachG67_movingKernel_paid 3 (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro ρ hρ δ hδ
  have hthird : 0 < δ/3 := by positivity
  obtain ⟨Ne, he⟩ := eventually_atTop.mp (goldbachBV_logCube_normalized C (δ/3) hthird)
  obtain ⟨ε₀, hε₀, hε₀u, hm⟩ :=
    goldbachWeight_G12Rough_allRetained_small_epsilon (δ/3) hthird
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Np, hNp, hn⟩ := hp ρ hρ ε hε (hεlt.trans_le hε₀u)
  obtain ⟨Nm, _, hnmain⟩ := hm ε hε hεlt
  refine ⟨max Np (max Nm Ne), by omega, ?_⟩
  intro N hN hEven
  obtain ⟨h6, h7⟩ := hn N (by omega) hEven
  have hb := he N (by omega)
  simp only [Real.rpow_ofNat] at h6 h7
  have h6paid := (sub_le_sub_left hb _).trans h6
  have h7paid := (sub_le_sub_left hb _).trans h7
  have hmain := hnmain N (by omega) hEven
  push_cast at hmain ⊢
  nlinarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
