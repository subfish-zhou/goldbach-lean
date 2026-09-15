import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitActual

/-! # Common-threshold payment with the same reciprocal mass -/
namespace Wu2008DoubleSieve
open Finset Real Filter
open scoped Classical

/-- The saving is positive for fixed parameters, not uniformly at the boundary. -/
theorem secondFunctionalUnit_beta_pos {δ s : ℝ} (hδ : 0 < δ) (hs : 2 < s) :
    0 < 1 - 4 * (1 / 2 - δ) / s := by
  have hs0 : 0 < s := by linarith
  have h : 4 * (1 / 2 - δ) / s < 1 := (div_lt_one hs0).mpr (by linarith)
  linarith

theorem secondFunctionalUnit_envelope_eq {N : ℕ} (hN : 0 < N) (δ s : ℝ) :
    ((N : ℝ) ^ (1 / 2 - δ)) ^ (4 / s) =
      (N : ℝ) / (N : ℝ) ^ (1 - 4 * (1 / 2 - δ) / s) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← rpow_mul hN0.le]
  calc
    _ = (N : ℝ) ^ (1 - (1 - 4 * (1 / 2 - δ) / s)) := by congr 1; ring
    _ = _ := by rw [rpow_sub hN0, rpow_one]

/-- Scalar threshold is selected before any finite carrier or weight family. -/
theorem secondFunctionalUnit_log_budget {δ s η : ℝ}
    (hδ : 0 < δ) (hs : 2 < s) (hη : 0 < η) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ((N : ℝ) ^ (1 / 2 - δ)) ^ (4 / s) ≤ η * ((N : ℝ) / log N) := by
  have hb := secondFunctionalUnit_beta_pos hδ hs
  obtain ⟨T, hT⟩ := eventually_atTop.mp (box_eventually_log_power_budget 1 (inv_pos.mpr hη) hb)
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpay := hT N ((le_max_right _ _).trans hN)
  simp only [pow_one] at hpay
  have hden : log (N : ℝ) ≤ η * (N : ℝ) ^ (1 - 4 * (1 / 2 - δ) / s) := by
    calc
      _ = η * (η⁻¹ * log (N : ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hpay hη.le
  rw [secondFunctionalUnit_envelope_eq (by omega) δ s]
  apply (div_le_iff₀ (rpow_pos_of_pos hN0 _)).mpr
  apply (le_of_eq (show (N : ℝ) = ((N : ℝ) / log N) * log N by field_simp)).trans
  calc
    _ ≤ ((N : ℝ) / log N) * (η * (N : ℝ) ^ (1 - 4 * (1 / 2 - δ) / s)) :=
      mul_le_mul_of_nonneg_left hden (div_nonneg hN0.le hlog.le)
    _ = _ := by ring

/-- One threshold pays both the original mass scale and the density-scaled
Theta scale. The auxiliary tolerance divides by K+1, never by K or a mass. -/
theorem secondFunctionalUnit_common_payment (k : ℕ) {δ s K ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 2 < s)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      let W := convolutionWuWindows N Δ V
      let E := ((N : ℝ) ^ (1 / 2 - δ)) ^ (4 / s) * boxConvolutionReciprocalMass W
      E ≤ ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W ∧
      E * (K * wuSingularSeries N / log N) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W ∧
      E ≤ ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  let η := ε / (K + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hηε : η ≤ ε := div_le_self hε.le (by linarith)
  have hηK : η * K / 2 ≤ ε := by
    have h : η * K ≤ ε := by
      apply (le_of_eq (show η * K = ε * (K / (K + 1)) by dsimp [η]; ring)).trans
      exact mul_le_of_le_one_right hε.le ((div_le_one (by linarith)).mpr (by linarith))
    linarith
  obtain ⟨T₁, hT₁4, hT₁⟩ := secondFunctionalUnit_log_budget hδ hs hη
  obtain ⟨T₂, hT₂4, hT₂⟩ := omega3_power_mass_relative k hδ hδhi hε
    (show (0 : ℝ) < 1 by norm_num) (secondFunctionalUnit_beta_pos hδ hs)
  refine ⟨max T₁ T₂, hT₁4.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb
  dsimp only
  have hN4 : 4 ≤ N := hT₂4.trans ((le_max_right _ _).trans hN)
  have hmass : 0 ≤ boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
    sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hdens : 0 ≤ K * wuSingularSeries N / log N :=
    div_nonneg (mul_nonneg hK (wuSingularSeries_pos N (by omega)).le) hlog.le
  have hsmall := mul_le_mul_of_nonneg_right (hT₁ N ((le_max_left _ _).trans hN)) hmass
  have hC0 := (wuSingularSeries_pos N (show 0 < N by omega)).le
  have htheta0 : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
    (by positivity : (0 : ℝ) ≤ 2 * wuSingularSeries N * (N : ℝ) / log N ^ 2 *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)).trans
        (omega3_source_theta_lower_singular hN4 hδ hδhi hb)
  refine ⟨hsmall.trans ?_, (mul_le_mul_of_nonneg_right hsmall hdens).trans ?_, ?_⟩
  · gcongr
  · exact (omega3X_scaled_error_le hN4 hδ hδhi hb hη.le hK).trans
      (mul_le_mul_of_nonneg_right hηK htheta0)
  · have hh := hT₂ N ((le_max_right _ _).trans hN) i Δ V hb
    rw [secondFunctionalUnit_envelope_eq (by omega) δ s]
    simpa only [one_mul] using hh

/-- Actual Gamma16 unit-density payment: no caller geometry or mass estimate. -/
theorem secondFunctionalUnitGamma16_common_payment (k : ℕ) {δ K ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      let W := convolutionWuWindows N Δ V
      secondFunctionalUnitGamma16 N δ W ≤
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W ∧
      secondFunctionalUnitGamma16 N δ W * (K * wuSingularSeries N / log N) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W ∧
      secondFunctionalUnitGamma16 N δ W ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  obtain ⟨T, hT4, hT⟩ := secondFunctionalUnit_common_payment k hδ hδhi
    (show (2 : ℝ) < 5 / 2 by norm_num) hK hε
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb
  have hN4 := hT4.trans hN
  have hU := secondFunctionalUnitGamma16_le (by omega) hδ hδhi hb
  have hp := hT N hN i Δ V hb
  have hdens : 0 ≤ K * wuSingularSeries N / log N :=
    div_nonneg (mul_nonneg hK (wuSingularSeries_pos N (by omega)).le)
      (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  exact ⟨hU.trans hp.1, (mul_le_mul_of_nonneg_right hU hdens).trans hp.2.1,
    hU.trans hp.2.2⟩

/-- The same threshold works for every finite four-coordinate carrier satisfying
only the local bounds. Future variable-window rows may use this theorem; their
profiles are not constructed here. -/
theorem secondFunctionalUnit_finite_common_payment (k : ℕ) {δ s K ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 2 < s) (hs3 : s ≤ 3)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      ∀ P : Finset Gamma16Profile, ∀ F : Gamma16Profile → Finset ℕ,
      (∀ c ∈ P, c.2.2.2.2 = 1 →
        c.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ∧
        (0 < c.2.1 ∧ (c.2.1 : ℝ) ≤ wuLocalCutoff N δ c.1 s) ∧
        (0 < c.2.2.1 ∧ (c.2.2.1 : ℝ) ≤ wuLocalCutoff N δ c.1 s) ∧
        (0 < c.2.2.2.1 ∧ (c.2.2.2.1 : ℝ) ≤ wuLocalCutoff N δ c.1 s)) →
      (∀ c ∈ P, c.2.2.2.2 = 1 → ∀ p ∈ F c,
        0 < p ∧ (p : ℝ) ≤ wuLocalCutoff N δ c.1 s) →
      let W := convolutionWuWindows N Δ V
      let U := ∑ c ∈ P.filter (fun c => c.2.2.2.2 = 1),
        (convolutionCoeff W c.1 : ℝ) * (F c).card
      U ≤ ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W ∧
      U * (K * wuSingularSeries N / log N) ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W ∧
      U ≤ ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  obtain ⟨T, hT4, hT⟩ := secondFunctionalUnit_common_payment k hδ hδhi hs hK hε
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb P F hP hF
  have hN4 := hT4.trans hN
  have hU := secondFunctionalUnit_mass_le (convolutionWuWindows N Δ V) P F
    (rpow_nonneg (Nat.cast_nonneg N) (1 / 2 - δ)) hs hs3
    (fun d hd => (omega3_source_support_le_Q (by omega) hδ hδhi hb hd).1) hP hF
  have hp := hT N hN i Δ V hb
  have hdens : 0 ≤ K * wuSingularSeries N / log N :=
    div_nonneg (mul_nonneg hK (wuSingularSeries_pos N (by omega)).le)
      (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  exact ⟨hU.trans hp.1, (mul_le_mul_of_nonneg_right hU hdens).trans hp.2.1,
    hU.trans hp.2.2⟩

end Wu2008DoubleSieve
