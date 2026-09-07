import MathlibNt.SieveTheory.LiLiuGoldbachSmallEpsilon

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A fixed six-term logarithm estimate, certified by an analytic remainder. -/
theorem goldbachS2_g3_scalar_le_84289 :
    8 * Real.log (10/9 : ℝ) ≤ (84289/100000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (by norm_num : (0 : ℝ) ≤ 1/19) (by norm_num : (1/19 : ℝ) < 1) 6
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The real S2 count retains the epsilon-dependent prime cutoff.
The epsilon bound precedes epsilon, then the threshold depends on epsilon. -/
theorem goldbachS2_g3_upper_84289_small_epsilon (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachS2 (goldbachDifferenceCarrier N ε) N
            ((N : ℝ)^((9 : ℝ)/19-ε)) : ℝ) ≤
            ((84289/100000 : ℝ)+δ)*
              (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨ε₀, hε₀, hε₀u, h⟩ := goldbachS2_g3_upper_small_epsilon δ hδ
  refine ⟨ε₀, hε₀, hε₀u, ?_⟩
  intro ε hε hεlt
  obtain ⟨N₀, hN₀, hN⟩ := h ε hε hεlt
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (hN N hNN hEven).trans (mul_le_mul_of_nonneg_right
    (add_le_add goldbachS2_g3_scalar_le_84289 (le_refl δ)) hs)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig