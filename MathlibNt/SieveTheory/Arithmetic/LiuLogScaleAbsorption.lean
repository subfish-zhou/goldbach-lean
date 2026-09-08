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

end MathlibNt.SieveTheory.LiuWeight
