import MathlibNt.Wu2008DoubleSieve.SeventhEighthClassicalSharpMass
import MathlibNt.Wu2008DoubleSieve.SeventhEighthPhysicalSieveEndpoint

namespace Wu2008DoubleSieve.SeventhEighth
open Real

/-- Both literal physical families have their classical coefficient eight.
All slack is fixed before the common threshold; no numerical Ji bounds are used. -/
theorem seventh_eighth_physical_classical_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((physicalT7 N).card : ℝ) ≤ (8 * J7 + ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) ∧
      ((physicalT8 N).card : ℝ) ≤ (8 * J8 + ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  let η := min 1 (ε / (J7 + J8 + 10))
  have h7 := J7_nonneg
  have h8 := J8_nonneg
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by linarith))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η * (J7 + J8 + 10) ≤ ε :=
    (le_div_iff₀ (by linarith : 0 < J7 + J8 + 10)).mp (min_le_right _ _)
  have hc7 : (8 + η) * (J7 + η) + η ≤ 8 * J7 + ε := by
    nlinarith [mul_le_mul_of_nonneg_left hη1 hη.le, mul_nonneg hη.le h8]
  have hc8 : (8 + η) * (J8 + η) + η ≤ 8 * J8 + ε := by
    nlinarith [mul_le_mul_of_nonneg_left hη1 hη.le, mul_nonneg hη.le h7]
  obtain ⟨Ts, hTs, hs⟩ := seventh_eighth_physical_upper_classicalMass hη
  obtain ⟨Tm, _, hm⟩ := seventh_eighth_classicalMass_le_J_add_epsilon hη
  refine ⟨max Ts Tm, hTs.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hNs := (le_max_left Ts Tm).trans hN
  have hNm := (le_max_right Ts Tm).trans hN
  have h512 := hTs.trans hNs
  have hNpos : 0 < N := by omega
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := (wuSingularSeries_pos N hNpos).le
  obtain ⟨hs7, hs8⟩ := hs N hNs he
  obtain ⟨hm7, hm8⟩ := hm N hNm
  have transfer (X M J : ℝ)
      (hx : X ≤ ((8 + η) * wuSingularSeries N / log N) * M +
        η * wuSingularSeries N * N / log N ^ (2 : ℕ))
      (hmass : M ≤ (J + η) * N / log N)
      (hc : (8 + η) * (J + η) + η ≤ 8 * J + ε) :
      X ≤ (8 * J + ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
    calc
      X ≤ ((8 + η) * wuSingularSeries N / log N) * ((J + η) * N / log N) +
          η * wuSingularSeries N * N / log N ^ (2 : ℕ) :=
        hx.trans (add_le_add
          (mul_le_mul_of_nonneg_left hmass
            (show 0 ≤ (8 + η) * wuSingularSeries N / log N by positivity)) le_rfl)
      _ = ((8 + η) * (J + η) + η) * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
        field_simp
      _ ≤ _ := by gcongr
  exact ⟨transfer _ _ _ hs7 hm7 hc7, transfer _ _ _ hs8 hm8 hc8⟩

/-- The original negative weights two and one, with a single total error. -/
theorem seventh_eighth_weighted_classical_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      2 * ((physicalT7 N).card : ℝ) + ((physicalT8 N).card : ℝ) ≤
        (16 * J7 + 8 * J8 + ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  obtain ⟨T, hT, hu⟩ := seventh_eighth_physical_classical_upper (show 0 < ε / 3 by positivity)
  refine ⟨T, hT, ?_⟩
  intro N hN he
  obtain ⟨h7, h8⟩ := hu N hN he
  ring_nf at h7 h8 ⊢
  linarith only [h7, h8]

end Wu2008DoubleSieve.SeventhEighth
