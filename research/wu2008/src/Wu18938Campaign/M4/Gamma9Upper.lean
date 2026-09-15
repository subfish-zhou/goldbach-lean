import Wu18938Campaign.M4.Gamma9Dictionary
import WR2GammaHighNormalized
import HighO3Actual
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalGamma9IntegralUpper
import MathlibNt.Wu2008DoubleSieve.HighSixOmega3Remainders

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh HighBoxRecovery Finset Real Filter
open scoped Classical Topology

private theorem window_geometry {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    (∀ k p, p ∈ windows j N k → p.Prime ∧ (N : ℝ) ^ highEta ≤ p) ∧
    (∀ d ∈ boxConvolutionSupport (windows j N),
      (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ - 10 * highEta)) :=
  ⟨fun _ _ hp => ⟨(prime_geometry j hN hd hh hp).1,
    (prime_geometry j hN hd hh hp).2.2.1⟩, support_size j hN hd hh⟩

theorem gamma9_R1_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ Z : ℝ,
      omega3SieveR1 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) δ s t Z (windows j N) ≤
        ε * truncatedSixthMassScale N := by
  obtain ⟨C, _, T0, hT04, hb⟩ := R1_total_slack 1 hd
    (show 0 < highEta by norm_num [highEta]) (show (0 : ℝ) < 3 by norm_num)
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨T1, hlogBudget⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C / (ε * wuSingularSeries 1))))
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN j s t hs hst ht Z
  have hl : 0 < log (N : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < N by omega))
  have hseries : wuSingularSeries 1 ≤ wuSingularSeries N :=
    wuSingularSeries_le_of_dvd (by norm_num) (by omega) (one_dvd N)
  have hc : C / log (N : ℝ) ≤ ε * wuSingularSeries N := by
    apply (div_le_iff₀ hl).mpr
    have h := (div_le_iff₀ (mul_pos heps hC1)).mp (hlogBudget N (by omega))
    have h' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hseries heps.le) hl.le
    dsimp only [Function.comp_apply] at h
    nlinarith
  have hg := window_geometry j (by omega : 2 ≤ N) hd hh
  calc
    _ ≤ C * N / log (N : ℝ) ^ (3 : ℝ) :=
      hb N (by omega) 1 le_rfl _ hg.1 hg.2 s t hs hst ht Z
    _ = (C / log N) * ((N : ℝ) / log N ^ 2) := by norm_num; ring
    _ ≤ (ε * wuSingularSeries N) * ((N : ℝ) / log N ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by unfold truncatedSixthMassScale; ring

theorem gamma9_R2_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      omega3SieveR2 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) δ s t
        (sqrt ((N : ℝ) ^ (1 / 2 - δ))) (windows j N) ≤
          ε * truncatedSixthMassScale N := by
  obtain ⟨C, hC, hb⟩ := R2_total_slack 1 hd (show δ < 1 / 2 by linarith)
    (show 0 < highEta by norm_num [highEta])
  have hk : 0 < 2 * C * (max 1 (1 / highEta)) ^ 3 / log 2 := by positivity
  obtain ⟨T0, hT04, hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 5 heps hk
    (show 0 < highEta by norm_num [highEta])
  obtain ⟨T1, hl⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN j s t hs hst ht
  have hN4 : 4 ≤ N := by omega
  have hlog := hl N (by omega)
  dsimp only [Function.comp_apply] at hlog
  have hg := window_geometry j (by omega : 2 ≤ N) hd hh
  calc
    _ ≤ C * (max 1 (1 / highEta)) ^ 3 * N *
        ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ highEta * log 2)) :=
      hb N hN4 1 le_rfl _ hg.1 hg.2 s t hs hst ht
    _ ≤ C * (max 1 (1 / highEta)) ^ 3 * N *
        ((2 * log N) * log N ^ 4 / ((N : ℝ) ^ highEta * log 2)) := by
      gcongr
      linarith
    _ = (2 * C * (max 1 (1 / highEta)) ^ 3 / log 2) * N *
        log N ^ 5 / (N : ℝ) ^ highEta := by ring
    _ ≤ _ := hp N (by omega)

theorem gamma9_upper_fixed {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      gamma j N δ 9 ≤
        (2 / (1 - 2 * δ)) *
          omega3XIntegralEnvelope (Wu04RemainingCore.row j).kappa3
            (Wu04RemainingCore.row j).kappa1 * theta j N δ +
          ε * truncatedSixthMassScale N := by
  have hdhi : δ < 1 / 2 := by linarith
  have he : 0 < ε / 1000 := by positivity
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨ρ, hρ, hslack⟩ := omega3_envelope_uniform_slack hdhi
    (show 0 < 3 * (ε / 1000) by positivity)
  have hK : 0 < HighO3.densityFactor δ ρ :=
    omega3X_fixed_density_factor_pos hdhi hρ
  obtain ⟨T0, hT04, hS⟩ := omega3_switched_upper_source_density hd hdhi hρ
  obtain ⟨T1, _, hX⟩ := HighO3.X_integral_scaled hd hdhi hη hK he
  obtain ⟨T2, _, hL⟩ := HighO3.losses_paid hd hdhi hη he
  obtain ⟨T3, _, hR1⟩ := gamma9_R1_paid hd hh (show 0 < ε / 4 by positivity)
  obtain ⟨T4, _, hR2⟩ := gamma9_R2_paid hd hh (show 0 < ε / 4 by positivity)
  obtain ⟨T5, _, hLi⟩ := omega3X_trueLi_sharp_lower hρ
  obtain ⟨T6, _, htheta⟩ := theta_integral_error (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T0 (max T1 (max T2 (max T3 (max T4 (max T5 T6))))),
    hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven j
  have hN4 : 4 ≤ N := by omega
  have hg := window_geometry j (by omega : 2 ≤ N) hd hh
  have hw := fun d hdm =>
    And.intro (boxConvolutionSupport_pos (fun k p hp => (hg.1 k p hp).1.pos) hdm)
      (hg.2 d hdm)
  let s := (Wu04RemainingCore.row j).kappa3
  let t := (Wu04RemainingCore.row j).kappa1
  have hp := (row_analytic j).mother
  have hs : 2 ≤ s := (row_analytic j).two_lt_s.le.trans hp.s_le_kappa3
  have hst : s ≤ t := hp.kappa3_lt_kappa2.le.trans hp.kappa2_lt_kappa1.le
  have ht : t ≤ 10 := hp.kappa1_le_S.trans hp.S_le_ten
  have hX' := hX N (by omega) 1 _ hw s t hs hst ht
  have hL' := hL N (by omega) hEven 1 _ hg.1 hg.2 s t hs hst ht
  have hS' := hS N (by omega) hEven 1 s t (windows j N)
  change _ ≤ omega3SieveX N δ s t (windows j N) *
    (HighO3.densityFactor δ ρ * wuSingularSeries N / log N) + _ + _ at hS'
  have henv := HighO3.integral_envelope_scaled (windows j N) hN4 hd hdhi hη hw
    hs hst ht hK.le (hLi N (by omega))
  have hfinite := HighO3.omega3_add_repeated_le_closed
    (δ := δ) (s := s) (t := t) (windows j N) hN4 hEven
    (fun k p hp' => (hg.1 k p hp').1)
  have hrep : 0 ≤ wuOmegaRepeatedSum N δ s t (windows j N) := by
    unfold wuOmegaRepeatedSum wuOmegaRepeated
    exact sum_nonneg (fun d _ => mul_nonneg (Nat.cast_nonneg _)
      (sum_nonneg (fun p _ => by unfold sourceSieveCount; positivity)))
  have hR1' := hR1 N (by omega) j s t hs hst ht (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
  have hR2' := hR2 N (by omega) j s t hs hst ht
  have hM := truncatedSixthClosure_scale_nonneg hN4
  have hm : theta j N δ ≤ 161 * truncatedSixthMassScale N := by
    have h := (abs_le.mp (htheta N (by omega) hEven j δ hd.le hh)).2
    have hI := mul_le_mul_of_nonneg_right (prime_integral_bounds j hh).2 hM
    linarith only [h, hI]
  have htheta0 := theta_nonneg j hN4 hd hh
  have hs' := mul_le_mul_of_nonneg_right (hslack s t hs hst ht) htheta0
  have hpay := mul_le_mul_of_nonneg_left hm (show 0 ≤ 3 * (ε / 1000) by positivity)
  change _ ≤ _ + (ε / 1000) * theta j N δ at hX'
  change _ ≤ (ε / 1000) * theta j N δ at hL'
  change _ ≤ _ * theta j N δ at henv
  change (1 + ρ) * HighO3.densityFactor δ ρ / 4 * omega3XIntegralEnvelope s t *
    theta j N δ ≤ _ at hs'
  rw [gamma9_eq_omega3 j (by omega) hd hh]
  change wuOmega3Sum N δ s t (windows j N) ≤ _
  nlinarith only [hfinite, hrep, hS', hX', hL', henv, hR1', hR2', hs', hpay, hM, heps]

end Wu18938Campaign.M4
