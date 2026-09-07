import MathlibNt.SieveTheory.LiLiuGoldbachPairLayerCoordinate

open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The ideal coordinate lies in a fixed positive interval for the pair range. -/
theorem pairLayer_ideal_coordinate_bounds (N m : ℕ) (hN : 4 ≤ N) (hm : 0 < m)
    (hml : (N : ℝ) ^ (8 / 53 : ℝ) ≤ (m : ℝ))
    (hmu : (m : ℝ) ≤ (N : ℝ) ^ (13 / 33 : ℝ)) :
    0 < (1 / 2 - Real.log (m : ℝ) / Real.log (N : ℝ)) / (4 / 53 : ℝ) ∧
    (1 / 2 - Real.log (m : ℝ) / Real.log (N : ℝ)) / (4 / 53 : ℝ) ≤ 37 / 8 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hl0 : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlow := Real.log_le_log (Real.rpow_pos_of_pos hN0 (8 / 53)) hml
  have hupp := Real.log_le_log hm0 hmu
  rw [Real.log_rpow hN0] at hlow hupp
  have hl : (8 / 53 : ℝ) ≤ Real.log (m : ℝ) / Real.log (N : ℝ) :=
    (le_div_iff₀ hl0).2 hlow
  have hu : Real.log (m : ℝ) / Real.log (N : ℝ) ≤ (13 / 33 : ℝ) :=
    (div_le_iff₀ hl0).2 (by simpa [mul_comm] using hupp)
  constructor
  · apply div_pos _ (by norm_num)
    linarith
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4 / 53)).2
    linarith

/-- Uniform fixed compact-range consumer; no prime or coprimality assumptions. -/
theorem exists_pairLayer_coordinate_lt_six (B : ℝ) (hB : 0 ≤ B) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ m : ℕ, 0 < m →
      (N : ℝ) ^ (8 / 53 : ℝ) ≤ (m : ℝ) →
      (m : ℝ) ≤ (N : ℝ) ^ (13 / 33 : ℝ) →
      (N : ℝ) ^ (7 / 132 : ℝ) ≤
        ((LiuWeight.panModulusCutoff N B / m + 1 : ℕ) : ℝ) ∧
      Real.log ((LiuWeight.panModulusCutoff N B / m + 1 : ℕ) : ℝ) /
        ((4 / 53 : ℝ) * Real.log (N : ℝ)) < 6 := by
  obtain ⟨N₀, hN₀, h⟩ := exists_pairLayer_coordinate_threshold B 1 hB (by norm_num)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN m hm hml hmu
  obtain ⟨hpower, herr⟩ := h N hN m hm hmu
  have hideal := pairLayer_ideal_coordinate_bounds N m (hN₀.trans hN) hm hml hmu
  exact ⟨hpower, by linarith [(abs_lt.mp herr).2, hideal.2]⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
