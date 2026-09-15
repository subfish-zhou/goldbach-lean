import MathlibNt.Wu2008DoubleSieve.Gamma5GainMain
import MathlibNt.Wu2008DoubleSieve.PositiveGainActual
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A fixed rational seed on the legal Gamma5 triangle

Only the triangle a <= t <= u <= 1/3 is used. The actual improvement
is measurable and integrable by the accepted monotonicity construction;
no continuity of the actual improvement is required.
-/

namespace Wu2008DoubleSieve
open Set Real Filter MeasureTheory
open scoped Interval

/-- The small triangle lies in the actual legal region. -/
theorem gamma5Seed_region {t u : ℝ} (ht : gamma5MassA ≤ t)
    (htu : t ≤ u) (hu : u ≤ 1 / 3) : (t, u) ∈ gamma5GainRegion := by
  have hb : (1 / 3 : ℝ) ≤ gamma5ClassicalB := by norm_num [gamma5ClassicalB]
  exact ⟨⟨ht, htu, hu.trans hb⟩, ⟨by linarith, by linarith⟩⟩

/-- Two polynomial factorizations give the reciprocal-kernel lower bound. -/
theorem gamma5Seed_product_le {t u : ℝ} (ht : gamma5MassA ≤ t)
    (htu : t ≤ u) (hu : u ≤ 1 / 3) : t * u * (1 - t - u) ≤ 1 / 27 := by
  have ht0 : 0 ≤ t := (by norm_num [gamma5MassA, gamma5ClassicalS] : (0 : ℝ) ≤ gamma5MassA).trans ht
  have hu0 : 0 ≤ u := ht0.trans htu
  have h1 : 0 ≤ u * (u - t) * (1 - t - 2 * u) :=
    mul_nonneg (mul_nonneg hu0 (sub_nonneg.mpr htu)) (by linarith)
  have h2 : 0 ≤ (1 / 3 - u) ^ 2 * (2 * u + 1 / 3) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith

/-- The actual kernel, not an assumed lower envelope, dominates 27/5000. -/
theorem gamma5Seed_kernel_lower {δ t u : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (ht : gamma5MassA ≤ t) (htu : t ≤ u) (hu : u ≤ 1 / 3) :
    (27 / 5000 : ℝ) ≤ gamma5GainKernel δ (t, u) := by
  have hr := gamma5Seed_region ht htu hu
  have hb := gamma5Gain_triangle_bounds hr.1
  have hv : gamma5GainV t u ≤ 29 / 10 := by
    have hau : gamma5MassA ≤ u := ht.trans htu
    norm_num [gamma5MassA, gamma5ClassicalS] at ht hau
    dsimp [gamma5GainV, gamma5ClassicalS]
    linarith
  have hh := positiveGain_actual_upper_range hδ hδhi hb.2.2.1.le hv
  rw [gamma5GainKernel, if_pos hr, gamma5GainH,
    gamma5Gain_clip_eq ⟨hb.2.2.1.le, hb.2.2.2.1.le⟩]
  apply (le_div_iff₀ hb.2.2.2.2).mpr
  have hd := gamma5Seed_product_le ht htu hu
  nlinarith

/-- The area of the fixed triangular witness is evaluated exactly. -/
theorem gamma5Seed_area :
    (∫ t in gamma5MassA..(1 / 3 : ℝ), ∫ _u in t..(1 / 3 : ℝ), (1 : ℝ)) =
      ((1 / 3 : ℝ) - gamma5MassA) ^ 2 / 2 := by
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  rw [intervalIntegral.integral_sub intervalIntegrable_const (show IntervalIntegrable (fun t : ℝ => t) volume gamma5MassA (1 / 3) from
    continuous_id.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
  ring

/-- Exact weighted area of the same triangle. -/
theorem gamma5Seed_weighted_area :
    (∫ t in gamma5MassA..(1 / 3 : ℝ), ((1 / 3 - t) * (27 / 5000))) =
      (147 / 6630625 : ℝ) := by
  rw [intervalIntegral.integral_mul_const]
  have ha := gamma5Seed_area
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at ha
  rw [ha]
  norm_num [gamma5MassA, gamma5ClassicalS]

/-- A rational positive lower bound on the existing literal legal-domain gain. -/
theorem gamma5GainIntegral_ge_seed_rational {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    (147 / 6630625 : ℝ) ≤ gamma5GainIntegral δ := by
  have hhalf : δ < 1 / 2 := by linarith
  have hab : gamma5MassA ≤ (1 / 3 : ℝ) := by norm_num [gamma5MassA, gamma5ClassicalS]
  have hbc : (1 / 3 : ℝ) ≤ gamma5ClassicalB := by norm_num [gamma5ClassicalB]
  let F : ℝ → ℝ := fun t => ∫ u, gamma5GainKernel δ (t, u)
  have hFi : Integrable F := (gamma5Gain_kernel_integrable hδ hhalf).integral_prod_left
  have hF0 : ∀ t, 0 ≤ F t := fun t =>
    integral_nonneg (fun u => (gamma5Gain_kernel_bounds hδ hhalf (t, u)).1)
  have heq : gamma5GainIntegral δ = ∫ t in gamma5MassA..gamma5ClassicalB, F t := by
    unfold gamma5GainIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    exact (gamma5Gain_inner_eq (by
      simpa only [uIcc_of_le (hab.trans hbc)] using ht)).symm
  have hinner (t : ℝ) (ht : t ∈ Icc gamma5MassA (1 / 3 : ℝ)) :
      (1 / 3 - t) * (27 / 5000) ≤ F t := by
    have htB : t ∈ Icc gamma5MassA gamma5ClassicalB := ⟨ht.1, ht.2.trans hbc⟩
    have hi := gamma5Gain_slice_integrable hδ hhalf t
    have hm : (∫ u in t..(1 / 3 : ℝ), (27 / 5000 : ℝ)) ≤
        ∫ u in t..(1 / 3 : ℝ), gamma5GainKernel δ (t, u) := by
      apply intervalIntegral.integral_mono_on ht.2 intervalIntegrable_const hi.intervalIntegrable
      intro u hu
      exact gamma5Seed_kernel_lower hδ hδhi ht.1 hu.1 hu.2
    have hsub := intervalIntegral.integral_mono_interval (f := fun u => gamma5GainKernel δ (t, u))
      le_rfl ht.2 hbc
      (Eventually.of_forall (fun u => (gamma5Gain_kernel_bounds hδ hhalf (t, u)).1))
      hi.intervalIntegrable
    have hfull : (∫ u in t..gamma5ClassicalB, gamma5GainKernel δ (t, u)) = F t := by
      rw [show F t = ∫ u in t..gamma5ClassicalB, gamma5GainLiteral δ t u from
        gamma5Gain_inner_eq htB]
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc t gamma5ClassicalB := by
        simpa only [uIcc_of_le htB.2] using hu
      exact gamma5Gain_kernel_eq_literal ht.1 hu'.1 hu'.2
    rw [hfull] at hsub
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm.trans hsub
  rw [heq, ← gamma5Seed_weighted_area]
  exact (intervalIntegral.integral_mono_on hab
      (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable _ _)
      hFi.intervalIntegrable hinner).trans
    (intervalIntegral.integral_mono_interval le_rfl hab hbc
      (Eventually.of_forall hF0) hFi.intervalIntegrable)

/-- All original labels and the original common-threshold quantifier order are retained. -/
theorem gamma5Gain_full_count_upper_seed_rational (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
        (gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V)) ≤
      (gamma5MassC5 - 147 / 6630625 + ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT, hcount⟩ := gamma5Gain_full_count_upper k hk hδ hδhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he i Δ V hb
  have htheta := gamma5Mass_theta_nonneg (show 2 ≤ N by omega) hδ (by linarith) hb
  exact (hcount N hN he i Δ V hb).trans
    (mul_le_mul_of_nonneg_right (by linarith [gamma5GainIntegral_ge_seed_rational hδ hδhi]) htheta)

end Wu2008DoubleSieve
