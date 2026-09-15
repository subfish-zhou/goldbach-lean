import MathlibNt.SieveTheory.Liu.PrimePairs.LiuPrimePairLogGridLimit

/-!
# Liu's prime-pair sum to integral transfer

This module combines the refining logarithmic-grid limit with the finite prime
limit for one fixed grid. The grid is chosen before the finite-`N` threshold,
preserving the quantifier order in Liu's source transfer.
-/

open Filter

namespace MathlibNt.SieveTheory.LiuWeight

noncomputable section

/-- Liu's finite reciprocal-log prime-pair sum is eventually bounded by the
source integral, with an arbitrary positive additive error. -/
theorem liuSourcePrimeSumToIntegralTransfer :
    LiuSourcePrimeSumToIntegralTransfer := by
  intro η hη
  have hηhalf : 0 < η / 2 := half_pos hη
  have hmesh := tendsto_liuLogGridUpperSum_sourceMainIntegral
  rw [Metric.tendsto_nhds] at hmesh
  have hmeshEventually :
      ∀ᶠ n : ℕ in atTop,
        dist (liuLogGridUpperSum (n + 1)) liuSourceMainIntegral < η / 2 :=
    hmesh (η / 2) hηhalf
  rw [eventually_atTop] at hmeshEventually
  obtain ⟨n, hn⟩ := hmeshEventually
  let m := n + 1
  have hm : 0 < m := by
    dsimp [m]
    omega
  have hupperAbs :
      |liuLogGridUpperSum m - liuSourceMainIntegral| < η / 2 := by
    simpa only [m, Real.dist_eq] using hn n (le_refl n)
  obtain ⟨N₁, hN₁⟩ :=
    exists_abs_liuLogGridMajorant_sub_lt m hm hηhalf
  refine ⟨max 8 N₁, fun N hN => ?_⟩
  have hN8 : 8 ≤ N := le_trans (le_max_left 8 N₁) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_right 8 N₁) hN
  have hmajorantAbs := hN₁ N hNN₁
  calc
    Real.log N * liuSourceReciprocalLogSum N = liuPairLogKernelSum N :=
      log_mul_liuSourceReciprocalLogSum_eq_pairLogKernelSum N hN8
    _ ≤ liuLogGridMajorant m N :=
      liuPairLogKernelSum_le_logGridMajorant m N hm hN8
    _ ≤ liuLogGridUpperSum m + η / 2 := by
      linarith [abs_lt.mp hmajorantAbs]
    _ ≤ liuSourceMainIntegral + η := by
      linarith [abs_lt.mp hupperAbs]

/-- Liu's exact source reciprocal-log estimate holds for all sufficiently large
`N`, unconditionally. -/
theorem eventually_liuSourceReciprocalLogBound :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → LiuSourceReciprocalLogBound N :=
  eventually_liuSourceReciprocalLogBound_of_transfer_of_constantBound
    liuSourcePrimeSumToIntegralTransfer
    liuSourceMainIntegralConstantBound

end
end MathlibNt.SieveTheory.LiuWeight
