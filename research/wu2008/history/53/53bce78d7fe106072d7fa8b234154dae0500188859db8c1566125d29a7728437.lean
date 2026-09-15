import R2OmegaHighCarrier

noncomputable section
namespace WuPaper.R2OmegaHigh
open Wu2008DoubleSieve WuSource.SrcSingle HighBoxRecovery
open Finset Real Filter
open scoped Classical Topology Interval BigOperators

theorem actual_R1_paid {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 4, ∀ Z : ℝ,
      omega3SieveR1 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) δ
        (psiNode (index j)) (psiTop (index j)) Z (windows j N) ≤
          ε * truncatedSixthMassScale N := by
  obtain ⟨C, _, T0, hT04, hb⟩ := R1_total_slack 1 hd
    (show 0 < highEta by norm_num [highEta]) (show (0 : ℝ) < 3 by norm_num)
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨T1, hlogBudget⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C / (ε * wuSingularSeries 1))))
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN j Z
  have hN4 : 4 ≤ N := hT04.trans (by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hs : wuSingularSeries 1 ≤ wuSingularSeries N :=
    wuSingularSeries_le_of_dvd (by norm_num) (by omega) (one_dvd N)
  have hc : C / log (N : ℝ) ≤ ε * wuSingularSeries N := by
    apply (div_le_iff₀ hl).mpr
    have h := (div_le_iff₀ (mul_pos heps hC1)).mp (hlogBudget N (by omega))
    have h' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs heps.le) hl.le
    dsimp only [Function.comp_apply] at h
    nlinarith
  have hg := support_geometry (N := N) j (by omega) hh
  have hp := geometry j
  calc
    _ ≤ C * N / log (N : ℝ) ^ (3 : ℝ) :=
      hb N (by omega) 1 le_rfl _ hg.1 hg.2 _ _ hp.1 hp.2.2.2.2.1
        (by linarith [hp.2.2.2.1]) Z
    _ = (C / log N) * ((N : ℝ) / log N ^ 2) := by norm_num; ring
    _ ≤ (ε * wuSingularSeries N) * ((N : ℝ) / log N ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by unfold truncatedSixthMassScale; ring

theorem actual_R2_paid {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 4,
      omega3SieveR2 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) δ
        (psiNode (index j)) (psiTop (index j))
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
  intro N hN j
  have hN4 : 4 ≤ N := hT04.trans (by omega)
  have hlog := hl N (by omega)
  dsimp only [Function.comp_apply] at hlog
  have hg := support_geometry (N := N) j (by omega) hh
  have hpar := geometry j
  calc
    _ ≤ C * (max 1 (1 / highEta)) ^ 3 * N *
        ((1 + log N) * log N ^ 4 / ((N : ℝ) ^ highEta * log 2)) :=
      hb N hN4 1 le_rfl _ hg.1 hg.2 _ _ hpar.1 hpar.2.2.2.2.1
        (by linarith [hpar.2.2.2.1])
    _ ≤ C * (max 1 (1 / highEta)) ^ 3 * N *
        ((2 * log N) * log N ^ 4 / ((N : ℝ) ^ highEta * log 2)) := by
      gcongr
      linarith
    _ = (2 * C * (max 1 (1 / highEta)) ^ 3 / log 2) * N *
        log N ^ 5 / (N : ℝ) ^ highEta := by ring
    _ ≤ _ := hp N (by omega)

theorem density_slack_choice (j : Fin 4) {δ ε : ℝ} (heps : 0 < ε) :
    ∃ ρ τ : ℝ, 0 < ρ ∧ 0 < τ ∧
      (1 + τ) * HighO3.densityFactor δ ρ / 4 *
        omega3XIntegralEnvelope (psiNode (index j)) (psiTop (index j)) ≤
      (2 / (1 - 2 * δ)) * omega3XIntegralEnvelope (psiNode (index j)) (psiTop (index j)) + ε := by
  let f : ℝ → ℝ := fun r => (1 + r) * HighO3.densityFactor δ r / 4 *
    omega3XIntegralEnvelope (psiNode (index j)) (psiTop (index j))
  have hc : ContinuousAt f 0 := by dsimp [f, HighO3.densityFactor]; fun_prop
  obtain ⟨r, hr, hb⟩ := Metric.continuousAt_iff.mp hc ε heps
  have hdist : dist (r / 2) (0 : ℝ) < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith
  have h := (abs_lt.mp (show |f (r / 2) - f 0| < ε by
    simpa only [Real.dist_eq] using hb hdist)).2
  have hf0 : f 0 = (2 / (1 - 2 * δ)) *
      omega3XIntegralEnvelope (psiNode (index j)) (psiTop (index j)) := by
    dsimp [f, HighO3.densityFactor]; ring
  refine ⟨r / 2, r / 2, half_pos hr, half_pos hr, ?_⟩
  rw [hf0] at h
  change f (r / 2) ≤ _
  linarith

theorem omega3_upper_at (j : Fin 4) {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (∑ p ∈ psiPrimes (index j) N,
        wuOmega3 N p δ (psiNode (index j)) (psiTop (index j))) ≤
      (2 / (1 - 2 * δ)) * omega3XIntegralEnvelope (psiNode (index j)) (psiTop (index j)) *
        theta j N δ + ε * truncatedSixthMassScale N := by
  have hdhi : δ < 1 / 2 := by linarith
  have he : 0 < ε / 1920 := by positivity
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨ρ, τ, hρ, hτ, hslack⟩ := density_slack_choice j (δ := δ) he
  have hK : 0 < HighO3.densityFactor δ ρ := omega3X_fixed_density_factor_pos hdhi hρ
  obtain ⟨T0, hT04, hS⟩ := omega3_switched_upper_source_density hd hdhi hρ
  obtain ⟨T1, _, hX⟩ := HighO3.X_integral_scaled hd hdhi hη hK he
  obtain ⟨T2, _, hL⟩ := HighO3.losses_paid hd hdhi hη he
  obtain ⟨T3, _, hR1⟩ := actual_R1_paid hd hh (show 0 < ε / 8 by positivity)
  obtain ⟨T4, _, hR2⟩ := actual_R2_paid hd hh (show 0 < ε / 8 by positivity)
  obtain ⟨T5, _, hLi⟩ := omega3X_trueLi_sharp_lower hτ
  obtain ⟨T6, _, hmass⟩ := theta_total_mass hd hh
  refine ⟨max T0 (max T1 (max T2 (max T3 (max T4 (max T5 T6))))),
    hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hN4 : 4 ≤ N := hT04.trans (by omega)
  have hg := support_geometry (N := N) j (by omega) hh
  have hw := fun d hdm =>
    And.intro (boxConvolutionSupport_pos (fun k p hp => (hg.1 k p hp).1.pos) hdm) (hg.2 d hdm)
  have hp := geometry j
  have ht10 : psiTop (index j) ≤ 10 := by linarith [hp.2.2.2.1]
  have hX' := hX N (by omega) 1 _ hw _ _ hp.1 hp.2.2.2.2.1 ht10
  have hL' := hL N (by omega) hEven 1 _ hg.1 hg.2 _ _ hp.1 hp.2.2.2.2.1 ht10
  have hS' := hS N (by omega) hEven 1 (psiNode (index j)) (psiTop (index j)) (windows j N)
  change _ ≤ omega3SieveX N δ (psiNode (index j)) (psiTop (index j)) (windows j N) *
    (HighO3.densityFactor δ ρ * wuSingularSeries N / log N) + _ + _ at hS'
  have henv := HighO3.integral_envelope_scaled (windows j N) hN4 hd hdhi hη hw
    hp.1 hp.2.2.2.2.1 ht10 hK.le (hLi N (by omega))
  have hrep : wuOmegaRepeatedSum N δ (psiNode (index j)) (psiTop (index j)) (windows j N) = 0 := by
    rw [wuOmegaRepeatedSum, weighted_sum]
    exact sum_eq_zero (fun p hpm => seven_repeated_zero (index j) (by omega) hd hh hpm)
  have hfinite := HighO3.omega3_add_repeated_le_closed
    (δ := δ) (s := psiNode (index j)) (t := psiTop (index j)) (windows j N) hN4 hEven
    (fun k p hpm => (hg.1 k p hpm).1)
  rw [hrep, add_zero, wuOmega3Sum, weighted_sum] at hfinite
  have hR1' := hR1 N (by omega) j (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
  have hR2' := hR2 N (by omega) j
  have hm := hmass N (by omega) hEven j
  have hs := mul_le_mul_of_nonneg_right hslack hm.1
  have hpay := mul_le_mul_of_nonneg_left hm.2 (show 0 ≤ 3 * (ε / 1920) by positivity)
  change _ ≤ _ + (ε / 1920) * theta j N δ at hX'
  change _ ≤ (ε / 1920) * theta j N δ at hL'
  change _ ≤ _ * theta j N δ at henv
  nlinarith only [hfinite, hS', hX', hL', henv, hR1', hR2', hs, hpay]

theorem omega3_upper {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 4,
      (∑ p ∈ psiPrimes (index j) N,
        wuOmega3 N p δ (psiNode (index j)) (psiTop (index j))) ≤
      (2 / (1 - 2 * δ)) * omega3XIntegralEnvelope (psiNode (index j)) (psiTop (index j)) *
        theta j N δ + ε * truncatedSixthMassScale N := by
  obtain ⟨T0, h0, h0'⟩ := omega3_upper_at 0 hd hh heps
  obtain ⟨T1, _, h1'⟩ := omega3_upper_at 1 hd hh heps
  obtain ⟨T2, _, h2'⟩ := omega3_upper_at 2 hd hh heps
  obtain ⟨T3, _, h3'⟩ := omega3_upper_at 3 hd hh heps
  refine ⟨max T0 (max T1 (max T2 T3)), h0.trans (le_max_left _ _), ?_⟩
  intro N hN he j
  fin_cases j
  · exact h0' N (by omega) he
  · exact h1' N (by omega) he
  · exact h2' N (by omega) he
  · exact h3' N (by omega) he

#check @WuPaper.R2OmegaHigh.actual_R1_paid
#check @WuPaper.R2OmegaHigh.actual_R2_paid
#check @WuPaper.R2OmegaHigh.density_slack_choice
#check @WuPaper.R2OmegaHigh.omega3_upper_at
#check @WuPaper.R2OmegaHigh.omega3_upper
#print axioms WuPaper.R2OmegaHigh.actual_R1_paid
#print axioms WuPaper.R2OmegaHigh.actual_R2_paid
#print axioms WuPaper.R2OmegaHigh.density_slack_choice
#print axioms WuPaper.R2OmegaHigh.omega3_upper_at
#print axioms WuPaper.R2OmegaHigh.omega3_upper
end WuPaper.R2OmegaHigh
