import MathlibNt.SieveTheory.LiLiuGoldbachB10LogGridLimit

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual finite `C10` weighted prime-pair mass whose one-sided limit is
controlled by Liu's printed integral `I10`. -/
noncomputable def goldbachB10ActualTriangleMass (N : ℕ) : ℝ :=
  goldbachB10PairLogKernelSum N

/-- The exact double integral `I10` from Liu's printed `(5.46)`. -/
noncomputable def goldbachB10I10 : ℝ :=
  goldbachB10MainIntegral

/-- The actual `C10` weighted prime-pair mass is eventually bounded above by
`I10 + η` for every fixed `η > 0`. -/
theorem goldbachB10ActualTriangleMass_le_I10_eventually
    {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachB10ActualTriangleMass N ≤ goldbachB10I10 + η := by
  have hηhalf : 0 < η / 2 := by positivity
  obtain ⟨n₀, hn₀⟩ :=
    exists_abs_goldbachB10LogGridUpperSum_sub_mainIntegral_lt hηhalf
  let n : ℕ := n₀ + 1
  have hn : 0 < n := by
    simp [n]
  have hgrid :
      goldbachB10LogGridUpperSum n ≤ goldbachB10MainIntegral + η / 2 := by
    have habs : |goldbachB10LogGridUpperSum n - goldbachB10MainIntegral| < η / 2 := by
      simpa [n] using hn₀ n₀ le_rfl
    linarith [abs_lt.mp habs]
  obtain ⟨N₁, hN₁⟩ :=
    exists_abs_goldbachB10LogGridMajorant_sub_lt n hn hηhalf
  let N₀ : ℕ := max 2 N₁
  refine ⟨N₀, le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := le_trans (le_max_left 2 N₁) hN
  have hclose := hN₁ N (le_trans (le_max_right 2 N₁) hN)
  have hmajorant :
      goldbachB10LogGridMajorant n N ≤ goldbachB10LogGridUpperSum n + η / 2 := by
    linarith [abs_lt.mp hclose]
  calc
    goldbachB10ActualTriangleMass N = goldbachB10PairLogKernelSum N := rfl
    _ ≤ goldbachB10LogGridMajorant n N :=
      goldbachB10PairLogKernelSum_le_logGridMajorant n N hn hN2
    _ ≤ goldbachB10LogGridUpperSum n + η / 2 := hmajorant
    _ ≤ goldbachB10I10 + η := by
      dsimp [goldbachB10I10]
      linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig