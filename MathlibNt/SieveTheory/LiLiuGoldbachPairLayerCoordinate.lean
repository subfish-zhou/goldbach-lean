import MathlibNt.SieveTheory.LiLiuGoldbachS3LevelGeometry

open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The genuine natural quotient has the same floor as the real quotient. -/
theorem pairLayer_floor_div (X : ℝ) (m : ℕ) :
    ⌊X⌋₊ / m = ⌊X / (m : ℝ)⌋₊ := by
  exact (Nat.floor_div_natCast X m).symm

/-- Exact rounding bounds for the natural layer, including its final `+1`. -/
theorem pairLayer_rounding (X : ℝ) (m : ℕ) (hY : 0 ≤ X / (m : ℝ)) :
    X / (m : ℝ) < ((⌊X⌋₊ / m + 1 : ℕ) : ℝ) ∧
      ((⌊X⌋₊ / m + 1 : ℕ) : ℝ) ≤ X / (m : ℝ) + 1 := by
  rw [pairLayer_floor_div]
  push_cast
  refine ⟨Nat.lt_floor_add_one _, ?_⟩
  linarith [Nat.floor_le hY]

/-- The floor perturbation contributes at most one to the logarithm. -/
theorem pairLayer_log_rounding (Y D : ℝ) (hY : 1 ≤ Y)
    (hlo : Y ≤ D) (hhi : D ≤ Y + 1) :
    0 ≤ Real.log D - Real.log Y ∧ Real.log D - Real.log Y ≤ 1 := by
  have hY0 : 0 < Y := by linarith
  have hD0 : 0 < D := lt_of_lt_of_le hY0 hlo
  refine ⟨sub_nonneg.mpr (Real.log_le_log hY0 hlo), ?_⟩
  rw [← Real.log_div hD0.ne' hY0.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos hD0 hY0)
  have hdiv : D / Y ≤ 2 := (div_le_iff₀ hY0).2 (by linarith)
  linarith

private theorem pairLayer_real_lower (N m : ℕ) (B : ℝ)
    (hN : 4 ≤ N) (hm : 0 < m)
    (hmu : (m : ℝ) ≤ (N : ℝ) ^ (13 / 33 : ℝ))
    (hlog : Real.log (N : ℝ) ^ B ≤ (N : ℝ) ^ (7 / 132 : ℝ)) :
    (N : ℝ) ^ (7 / 132 : ℝ) ≤
      ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B) / (m : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hl0 : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  apply (le_div_iff₀ hm0).2
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hl0 B)).2
  calc
    (N : ℝ) ^ (7 / 132 : ℝ) * m * Real.log (N : ℝ) ^ B ≤
        (N : ℝ) ^ (7 / 132 : ℝ) * (N : ℝ) ^ (13 / 33 : ℝ) *
          (N : ℝ) ^ (7 / 132 : ℝ) := by gcongr
    _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      norm_num

/-- Uniform power lower bound and absolute logarithmic coordinate control for
`Q / m + 1`, where the quotient and the addition are both in `ℕ`. -/
theorem pairLayer_coordinate_eventually (B η : ℝ) (hB : 0 ≤ B) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ ∀ m : ℕ, 0 < m →
      (m : ℝ) ≤ (N : ℝ) ^ (13 / 33 : ℝ) →
      (N : ℝ) ^ (7 / 132 : ℝ) ≤
        ((LiuWeight.panModulusCutoff N B / m + 1 : ℕ) : ℝ) ∧
      |Real.log ((LiuWeight.panModulusCutoff N B / m + 1 : ℕ) : ℝ) /
          ((4 / 53 : ℝ) * Real.log (N : ℝ)) -
        (1 / 2 - Real.log (m : ℝ) / Real.log (N : ℝ)) / (4 / 53 : ℝ)| < η := by
  let δ : ℝ := η * (4 / 53) / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hpower := LiuWeight.eventually_pan_log_rpow_le_rpow B (7 / 132) (by norm_num)
  have hsmall := LiuWeight.eventually_pan_log_rpow_le_rpow B δ hδ
  have hlarge : ∀ᶠ N : ℕ in atTop,
      max 1 (1 / δ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (4 : ℕ), hpower, hsmall, hlarge]
    with N hN hp hs hl
  refine ⟨hN, ?_⟩
  intro m hm hmu
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hl1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hl
  have hl0 : 0 < Real.log (N : ℝ) := by linarith
  have hpaid : 1 ≤ δ * Real.log (N : ℝ) := by
    have h := (le_max_right (1 : ℝ) (1 / δ)).trans hl
    exact (div_le_iff₀ hδ).mp h |>.trans_eq (mul_comm _ _)
  have hloss0 : 0 ≤ B * Real.log (Real.log (N : ℝ)) :=
    mul_nonneg hB (Real.log_nonneg hl1)
  have hloss : B * Real.log (Real.log (N : ℝ)) ≤ δ * Real.log (N : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hl0 B) hs
    rwa [Real.log_rpow hl0, Real.log_rpow hN0] at h
  let X : ℝ := (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B
  let Y : ℝ := X / (m : ℝ)
  let D : ℕ := LiuWeight.panModulusCutoff N B / m + 1
  have hYlow : (N : ℝ) ^ (7 / 132 : ℝ) ≤ Y :=
    pairLayer_real_lower N m B hN hm hmu hp
  have hY1 : 1 ≤ Y :=
    (Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega))
      (by norm_num : (0 : ℝ) ≤ 7 / 132)).trans hYlow
  have hX0 : 0 < X := div_pos (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos hl0 _)
  have hY0 : 0 < Y := div_pos hX0 hm0
  have hQ : LiuWeight.panModulusCutoff N B = ⌊X⌋₊ := by
    rw [LiuWeight.panModulusCutoff_eq_upper]
    congr 1
    rw [AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer.upperConductor,
      AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer.lowConductor,
      Real.sqrt_eq_rpow]
  have hr : Y < (D : ℝ) ∧ (D : ℝ) ≤ Y + 1 := by
    dsimp [D, Y]
    rw [hQ]
    exact pairLayer_rounding X m hY0.le
  refine ⟨hYlow.trans hr.1.le, ?_⟩
  have he := pairLayer_log_rounding Y (D : ℝ) hY1 hr.1.le hr.2
  have hlogY : Real.log Y = (1 / 2 : ℝ) * Real.log (N : ℝ) -
      B * Real.log (Real.log (N : ℝ)) - Real.log (m : ℝ) := by
    dsimp [Y, X]
    rw [Real.log_div hX0.ne' hm0.ne',
      Real.log_div (Real.rpow_pos_of_pos hN0 _).ne'
        (Real.rpow_pos_of_pos hl0 _).ne', Real.log_rpow hN0, Real.log_rpow hl0]
  have hden : 0 < (4 / 53 : ℝ) * Real.log (N : ℝ) := by positivity
  have hid : Real.log (D : ℝ) / ((4 / 53 : ℝ) * Real.log (N : ℝ)) -
      (1 / 2 - Real.log (m : ℝ) / Real.log (N : ℝ)) / (4 / 53 : ℝ) =
      ((Real.log (D : ℝ) - Real.log Y) - B * Real.log (Real.log (N : ℝ))) /
        ((4 / 53 : ℝ) * Real.log (N : ℝ)) := by
    rw [hlogY]
    field_simp
    ring
  change |Real.log (D : ℝ) / ((4 / 53 : ℝ) * Real.log (N : ℝ)) -
      (1 / 2 - Real.log (m : ℝ) / Real.log (N : ℝ)) / (4 / 53 : ℝ)| < η
  rw [hid, abs_div, abs_of_pos hden]
  apply (div_lt_iff₀ hden).2
  apply abs_lt.mpr
  dsimp [δ] at hloss hpaid
  constructor <;> nlinarith [mul_pos hη hden]

/-- One threshold is chosen before the whole varying modulus range. -/
theorem exists_pairLayer_coordinate_threshold (B η : ℝ) (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ m : ℕ, 0 < m →
      (m : ℝ) ≤ (N : ℝ) ^ (13 / 33 : ℝ) →
      (N : ℝ) ^ (7 / 132 : ℝ) ≤
        ((LiuWeight.panModulusCutoff N B / m + 1 : ℕ) : ℝ) ∧
      |Real.log ((LiuWeight.panModulusCutoff N B / m + 1 : ℕ) : ℝ) /
          ((4 / 53 : ℝ) * Real.log (N : ℝ)) -
        (1 / 2 - Real.log (m : ℝ) / Real.log (N : ℝ)) / (4 / 53 : ℝ)| < η := by
  obtain ⟨N₀, hN₀⟩ := (eventually_atTop.1 (pairLayer_coordinate_eventually B η hB hη))
  exact ⟨max 4 N₀, le_max_left _ _, fun N hN =>
    (hN₀ N ((le_max_right _ _).trans hN)).2⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
