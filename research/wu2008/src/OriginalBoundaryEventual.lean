import OriginalBoundaryPrime
noncomputable section
open scoped BigOperators Topology
open Filter Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.PrimeReciprocalLogRectangle
open MathlibNt.SieveTheory.PrimeReciprocalLogScale
namespace OriginalU8.Weighted
theorem original_kernel_le_upperSum_eventually
    (n : ℕ) (hn : 0 < n) (ρ h δ η : ℝ) (hρ : 1 < ρ)
    (hh : 0 < h) (hhsmall : h ≤ 1/20) (hδ : δ ≤ 1/4) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      relaxedPairKernel N ρ δ ≤ upperSum (100/1327) n h δ + η := by
  have hc := (Metric.tendsto_nhds.1
    (fixed_grid_tendsto (100/1327) n hn h δ)) η hη
  have he : ∀ᶠ N : ℕ in atTop,
      relaxedPairKernel N ρ δ ≤ upperSum (100/1327) n h δ + η := by
    filter_upwards [hc, fouvryG9RelaxedIntegral_curve_eventually ρ h hρ hh,
      eventually_ge_atTop (2 : ℕ)] with N hconv hw hN
    have habs : |grid (100/1327) n N h δ -
        upperSum (100/1327) n h δ| < η := by simpa only [Real.dist_eq] using hconv
    exact (original_kernel_le_grid n N hn hN hρ hδ hhsmall hw).trans
      (by have := (abs_lt.mp habs).2; linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp he
  exact ⟨max 4 N₁, le_max_left _ _, fun N hN => hN₁ N ((le_max_right _ _).trans hN)⟩

theorem upperSum_delta {n : ℕ} (hn : 0 < n)
    (h : ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/8) :
    upperSum (100/1327) n h δ ≤
      (1+6*δ)*upperSum (100/1327) n h 0 := by
  unfold upperSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  have ha := goldbachB9AlphaGridPoint_pos n q.1
  have hb := goldbachB9BetaGridPoint_pos n q.2
  have ha' := (goldbachB9AlphaGridPoint_lt_succ (i := q.1) hn).le
  have hb' := (goldbachB9BetaGridPoint_lt_succ (i := q.2) hn).le
  have hm : 0 ≤ logarithmicRectangleMass
      (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1+1))
      (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2+1)) := by
    exact mul_nonneg (Real.log_nonneg ((one_le_div ha).mpr ha'))
      (Real.log_nonneg ((one_le_div hb).mpr hb'))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (fouvryG9RelaxedIntegral_corner_delta hn hδ0 hδ q) hm


end OriginalU8.Weighted
