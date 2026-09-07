import MathlibNt.SieveTheory.LiLiuGoldbachB8LogGrid

open Filter
open scoped Topology

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The mesh is fixed before the prime-size limit. -/
theorem tendsto_goldbachB8LogGridMajorant (n : ℕ) (hn : 0 < n) :
    Tendsto (goldbachB8LogGridMajorant n) atTop (nhds (goldbachB8LogGridUpperSum n)) := by
  unfold goldbachB8LogGridMajorant goldbachB8LogGridUpperSum
  apply PrimeReciprocalLogRectangle.tendsto_weighted_sum_primeReciprocalLogRectangle
  · intro q _
    exact goldbachB8AlphaGridPoint_pos n q.1
  · intro q _
    exact goldbachB8AlphaGridPoint_lt_succ hn
  · intro q _
    exact goldbachB8BetaGridPoint_pos n q.2
  · intro q _
    exact goldbachB8BetaGridPoint_lt_succ hn

/-- Actual finite kernel bounded by the fixed-mesh limit, with the prime-size
threshold after the mesh and tolerance. No mesh-to-integral limit is assumed. -/
theorem goldbachB8PairLogKernel_le_gridUpperSum_eventually
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachB8PairLogKernel N ≤ goldbachB8LogGridUpperSum n + η := by
  have hc := (Metric.tendsto_nhds.1 (tendsto_goldbachB8LogGridMajorant n hn)) η hη
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hc
  refine ⟨max 2 N₁, le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hh : |goldbachB8LogGridMajorant n N - goldbachB8LogGridUpperSum n| < η := by
    simpa only [Real.dist_eq] using hN₁ N ((le_max_right _ _).trans hN)
  exact (goldbachB8PairLogKernel_le_logGridMajorant n N hn hN2).trans (by
    have hp := (abs_lt.mp hh).2
    linarith)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig