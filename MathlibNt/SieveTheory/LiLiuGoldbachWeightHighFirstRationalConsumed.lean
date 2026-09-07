import MathlibNt.SieveTheory.LiLiuGoldbachS5HighScalarScalar
import MathlibNt.SieveTheory.LiLiuGoldbachPositiveScalarClosed
import MathlibNt.SieveTheory.LiLiuGoldbachWeightHighFirstConsumed

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The strict-low count remains literal. This theorem does not assert positivity. -/
theorem goldbachWeight_highFirst_rational_consumed_small_epsilon
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightLowFirstRemainder (goldbachDifferenceCarrier N ε) N
            ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
            ((N : ℝ)^(3/11 : ℝ)) : ℝ) +
            ((62033529/100000000 : ℝ) - 392796161/100000000 - δ)*
              (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
            4*(D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, hε₀u, h⟩ :=
    goldbachWeight_remainingFive_rationalPositiveScalar_small_epsilon (δ/2) (by positivity)
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nr, hNr, hr⟩ := h ε hε hεlt
  obtain ⟨Ns, _hNs, hs⟩ := goldbachS5HighFirstClosed_normalized_upper_392796161
    (δ/2) ε (by positivity) hε (hεlt.trans_le hε₀u)
  refine ⟨max Nr Ns, hNr.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hbase := hr N ((le_max_left _ _).trans hN) hEven
  have hupper := hs N ((le_max_right _ _).trans hN) hEven
  have hN4 : 4 ≤ N := hNr.trans ((le_max_left _ _).trans hN)
  have hz : (N : ℝ)^(4/53 : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  rw [goldbachWeightRemainingFive_eq_lowFirstRemainder_sub_high _ _ _ _ _ hz] at hbase
  push_cast at hbase
  nlinarith [hbase, hupper]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig