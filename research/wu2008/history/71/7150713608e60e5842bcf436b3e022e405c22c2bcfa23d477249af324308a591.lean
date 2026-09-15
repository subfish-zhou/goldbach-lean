import MathlibNt.Wu2008DoubleSieve.Gamma6BaseMain

/-! # Actual full Gamma6 count with the literal C6 coefficient -/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology Interval

theorem gamma6Base_C6_literal :
    gamma6BaseC6 = ∫ t in (25 / 103 : ℝ)..(25 / 89),
      ∫ u in (100 / 291 : ℝ)..(2 / 5), 1 / (t * u * (1 - t - u)) := by
  rfl

theorem gamma6Base_C6_bounds : 0 ≤ gamma6BaseC6 ∧ gamma6BaseC6 ≤ 64 :=
  gamma6Base_integral_bounds le_rfl gamma6Base_constants.2.1.le le_rfl
    le_rfl gamma6Base_constants.2.2.2.1.le le_rfl

theorem gamma6Base_C6_integrable :
    (∀ t ∈ Icc (25 / 103 : ℝ) (25 / 89),
      IntervalIntegrable (fun u => 1 / (t * u * (1 - t - u))) volume (100 / 291) (2 / 5)) ∧
    IntervalIntegrable
      (fun t => ∫ u in (100 / 291 : ℝ)..(2 / 5), 1 / (t * u * (1 - t - u)))
      volume (25 / 103) (25 / 89) := by
  constructor
  · intro t ht
    exact gamma6Base_inner_integrable ht.1 ht.2 le_rfl gamma6Base_constants.2.2.2.1.le le_rfl
  · exact gamma6Base_outer_integrable le_rfl gamma6Base_constants.2.1.le le_rfl
      le_rfl gamma6Base_constants.2.2.2.1.le le_rfl

theorem gamma6Base_rectangle_count_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ A B C D : ℝ,
      gamma5MassA ≤ A → A ≤ B → B ≤ gamma6BaseB →
      gamma6BaseC ≤ C → C ≤ D → D ≤ gamma6BaseF →
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
        (gamma6BaseRectLabels N δ (convolutionWuWindows N Δ V) A B C D) ≤
      (gamma6BaseIntegral A B C D + ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let τ := min 1 (ε / 512)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : τ ≤ ε / 512 := min_le_right _ _
  obtain ⟨TC, hTC4, hcount⟩ := gamma6Base_mask_upper k hk hδ hδhi hτ hτ
  obtain ⟨TM, hTM4, hmass⟩ := gamma6Base_rectangle_mass k hk hδ hδhi hτ
  refine ⟨max TC TM, hTC4.trans (le_max_left _ _), ?_⟩
  intro N hNT he i Δ V hb A B C D hA hAB hB hC hCD hD
  have hNC : TC ≤ N := (le_max_left _ _).trans hNT
  have hNM : TM ≤ N := (le_max_right _ _).trans hNT
  have hN2 : 2 ≤ N := by omega
  have htheta := gamma5Mass_theta_nonneg hN2 hδ (by linarith) hb
  have hM := hmass N hNM i Δ V hb A B C D hA hAB hB hC hCD hD
  have hU := hcount N hNC he i Δ V hb
    (gamma6BaseRectLabels N δ (convolutionWuWindows N Δ V) A B C D)
    (filter_subset _ _)
  have hI := gamma6Base_integral_bounds hA hAB hB hC hCD hD
  have hbudget := gamma5Mass_scalar_budget hI.1 hI.2 hτ.le hτ1 hτε
  have hmain :
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma6BaseRectLabels N δ (convolutionWuWindows N Δ V) A B C D) ≤
        (gamma6BaseIntegral A B C D + τ) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
    linarith [(le_abs_self _).trans hM]
  have hmain' := mul_le_mul_of_nonneg_left hmain (sq_nonneg (1 + τ))
  have hbudget' := mul_le_mul_of_nonneg_right hbudget htheta
  nlinarith

/-- Full original half-open source labels, with no supplied estimate. -/
theorem gamma6Base_full_count_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
        (gamma6BaseLabels N δ (convolutionWuWindows N Δ V)) ≤
      (gamma6BaseC6 + ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT, h⟩ := gamma6Base_rectangle_count_upper k hk hδ hδhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he i Δ V hb
  have hh := h N hN he i Δ V hb gamma5MassA gamma6BaseB gamma6BaseC gamma6BaseF
    le_rfl gamma6Base_constants.2.1.le le_rfl le_rfl gamma6Base_constants.2.2.2.1.le le_rfl
  rw [gamma6Base_full_labels_eq (by omega) hδ (by linarith) hb] at hh
  exact hh

theorem gamma6Base_full_count_literal (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
        (gamma6BaseLabels N δ (convolutionWuWindows N Δ V)) ≤
      ((∫ t in (25 / 103 : ℝ)..(25 / 89),
        ∫ u in (100 / 291 : ℝ)..(2 / 5), 1 / (t * u * (1 - t - u))) + ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  simpa only [← gamma6Base_C6_literal] using gamma6Base_full_count_upper k hk hδ hδhi hε

end Wu2008DoubleSieve
