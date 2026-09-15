import MathlibNt.Wu2008DoubleSieve.FourRoughClassicalSharpMass
import MathlibNt.Wu2008DoubleSieve.LastPrimeFourPhysicalSieveEndpoint

namespace Wu2008DoubleSieve.FourClassical
open Real FourRoughClosedMass

/-- Both literal physical families have their classical coefficient eight.
All slack is fixed before the common threshold; no numerical Ji bounds are used. -/
theorem physical10_physical11_classical_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((TruncatedFourPhysical.Physical10 N).card : ℝ) ≤ (8 * I10 + ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) ∧
      ((TruncatedFourPhysical.Physical11 N).card : ℝ) ≤ (8 * I11 + ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  let η := min 1 (ε / (I10 + I11 + 10))
  have h7 := integrals_nonneg.1
  have h8 := integrals_nonneg.2
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by linarith))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η * (I10 + I11 + 10) ≤ ε :=
    (le_div_iff₀ (by linarith : 0 < I10 + I11 + 10)).mp (min_le_right _ _)
  have hc7 : (8 + η) * (I10 + η) + η ≤ 8 * I10 + ε := by
    nlinarith [mul_le_mul_of_nonneg_left hη1 hη.le, mul_nonneg hη.le h8]
  have hc8 : (8 + η) * (I11 + η) + η ≤ 8 * I11 + ε := by
    nlinarith [mul_le_mul_of_nonneg_left hη1 hη.le, mul_nonneg hη.le h7]
  obtain ⟨Ts, hTs, hs⟩ := LastPrimeFour.physical10_physical11_upper_rawMass hη
  obtain ⟨Tm, _, hm⟩ := rawMass_integral_sharp_bounds hη
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
      (hmass : M ≤ (J + η) * (N / log N))
      (hc : (8 + η) * (J + η) + η ≤ 8 * J + ε) :
      X ≤ (8 * J + ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
    calc
      X ≤ ((8 + η) * wuSingularSeries N / log N) * ((J + η) * (N / log N)) +
          η * wuSingularSeries N * N / log N ^ (2 : ℕ) :=
        hx.trans (add_le_add
          (mul_le_mul_of_nonneg_left hmass
            (show 0 ≤ (8 + η) * wuSingularSeries N / log N by positivity)) le_rfl)
      _ = ((8 + η) * (J + η) + η) * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
        field_simp
      _ ≤ _ := by gcongr
  exact ⟨transfer _ _ _ hs7 hm7 hc7, transfer _ _ _ hs8 hm8 hc8⟩

/-- The original negative weights one and one, with a single total error. -/
theorem physical10_physical11_sum_classical_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((TruncatedFourPhysical.Physical10 N).card : ℝ) + ((TruncatedFourPhysical.Physical11 N).card : ℝ) ≤
        (8 * I10 + 8 * I11 + ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  obtain ⟨T, hT, hu⟩ := physical10_physical11_classical_upper (show 0 < ε / 2 by positivity)
  refine ⟨T, hT, ?_⟩
  intro N hN he
  obtain ⟨h7, h8⟩ := hu N hN he
  ring_nf at h7 h8 ⊢
  linarith only [h7, h8]

end Wu2008DoubleSieve.FourClassical
