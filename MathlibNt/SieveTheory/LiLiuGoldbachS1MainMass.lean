import MathlibNt.SieveTheory.BombieriVinogradov

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A lower bound for the genuine AP main mass at the strict prime endpoint.
The endpoint is the greatest integer strictly below `(1-epsilon)*N`.
No new prime number theorem or distribution premise is used. -/
theorem goldbachS1_strictEndpoint_mainMass_lower (ε η : ℝ)
    (hε : 0 < ε) (hεu : ε < 1) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let m : ℕ := ⌈(1 - ε) * (N : ℝ)⌉₊ - 1
      2 ≤ m ∧ m ≤ N ∧
        (1 - ε - η) * ((N : ℝ) / Real.log (N : ℝ)) ≤
          BombieriVinogradov.trueLogarithmicIntegral (m : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (max (3 / (1 - ε)) (1 / η))
  refine ⟨max 2 k, le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast ((le_max_right 2 k).trans hN)
  have hx3 : 3 ≤ (1 - ε) * (N : ℝ) := by
    have hh := (div_le_iff₀ (sub_pos.mpr hεu)).mp ((le_max_left _ _).trans (hk.trans hkN))
    nlinarith
  have hηN : 1 ≤ η * (N : ℝ) := by
    have hh := (div_le_iff₀ hη).mp ((le_max_right _ _).trans (hk.trans hkN))
    nlinarith
  let m : ℕ := ⌈(1 - ε) * (N : ℝ)⌉₊ - 1
  have hceil3 : 3 ≤ ⌈(1 - ε) * (N : ℝ)⌉₊ := by
    exact_mod_cast hx3.trans (Nat.le_ceil ((1 - ε) * (N : ℝ)))
  have hm2 : 2 ≤ m := by dsimp [m]; omega
  have hmcast : (m : ℝ) = (⌈(1 - ε) * (N : ℝ)⌉₊ : ℝ) - 1 := by
    dsimp [m]
    rw [Nat.cast_sub (by omega)]
    simp only [Nat.cast_one]
  have hmlower : (1 - ε) * (N : ℝ) - 1 ≤ (m : ℝ) := by
    rw [hmcast]
    linarith [Nat.le_ceil ((1 - ε) * (N : ℝ))]
  have hmupper : (m : ℝ) ≤ N := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (1 - ε) * (N : ℝ) by linarith)
    rw [hmcast]
    nlinarith [mul_nonneg hε.le (Nat.cast_nonneg N)]
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogmono := Real.log_le_log (show 0 < (m : ℝ) by exact_mod_cast (show 0 < m by omega)) hmupper
  refine ⟨hm2, by exact_mod_cast hmupper, ?_⟩
  calc
    _ = ((1 - ε - η) * (N : ℝ)) / Real.log (N : ℝ) := by ring
    _ ≤ (m : ℝ) / Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right (by nlinarith) hlogN.le
    _ ≤ (m : ℝ) / Real.log (m : ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg m) hlogm hlogmono
    _ ≤ BombieriVinogradov.trueLogarithmicIntegral (m : ℝ) := by
      exact LiuWeight.div_log_le_liuLogarithmicIntegral (by exact_mod_cast hm2)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig