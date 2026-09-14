import MathlibNt.AnalyticNumberTheory.LargeSieve.LogPowerBounds

namespace AnalyticNumberTheory.LargeSieve

/-- A horizontal error with coefficient at most the height is paid by the tail budget. -/
theorem pointwiseSW_horizontal_le_tail
    {X ε T Q L : ℝ} (hX : 0 ≤ X) (hε : 0 < ε) (hT : 0 < T)
    (hQ : Q ≤ T) :
    Q * X / (ε * (1 + T ^ 2)) ≤ X * (1 + L ^ 2) / (ε * T) := by
  calc
    Q * X / (ε * (1 + T ^ 2)) ≤ T * X / (ε * (1 + T ^ 2)) := by
      gcongr
    _ ≤ X / (ε * T) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [mul_nonneg hX hε.le]
    _ ≤ X * (1 + L ^ 2) / (ε * T) := by
      gcongr
      nlinarith [sq_nonneg L]

end AnalyticNumberTheory.LargeSieve
