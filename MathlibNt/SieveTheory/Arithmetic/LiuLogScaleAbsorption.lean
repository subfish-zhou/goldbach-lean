import MathlibNt.Analysis.LogScaleAbsorption
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

open Filter
namespace MathlibNt.SieveTheory.LiuWeight

/-- An inverse-log remainder is absorbed into an arbitrary positive multiple of
the genuine Liu singular-series scale.  The uniform lower bound is the positive
universal Euler product, since every divisor correction factor is at least one. -/
theorem eventually_inverse_log_remainder_le_liuSingularSeries
    (C ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) ≤
        ρ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
  filter_upwards
    [MathlibNt.Analysis.eventually_log_rpow_remainder_lt_of_lower_bound
      C SingularSeries.liuUniversalProduct ρ 1
      SingularSeries.liuUniversalProduct_pos hρ (by norm_num)] with N hN
  have h := (hN 2 (SingularSeries.liuSingularSeries N)
    (SingularSeries.liuUniversalProduct_le_liuSingularSeries N)).le
  norm_num [Real.rpow_natCast] at h
  exact h

/-- A positive quartic-log remainder is eventually below any positive multiple
of the universal Liu product scale, with the natural threshold at least four. -/
theorem quartic_log_error_absorb_eventually
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) ≤
        δ * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
  -- Normalize the positive paid coefficient to its absolute-value envelope.
  have hbase :=
    MathlibNt.Analysis.eventually_log_rpow_remainder_lt_of_lower_bound
      |C| SingularSeries.liuUniversalProduct δ 2
      SingularSeries.liuUniversalProduct_pos hδ (by norm_num)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hbase
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN
  have h := (hM N ((le_max_right _ _).trans hN)
    2 SingularSeries.liuUniversalProduct le_rfl).le
  simpa only [abs_of_pos hC, show (2 : ℝ) + 2 = 4 by norm_num] using h

end MathlibNt.SieveTheory.LiuWeight
