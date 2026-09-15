import MathlibNt.Wu2008DoubleSieve.Gamma5MassMain

/-!
# Actual fully normalized classical Gamma5 count

The coefficient C5 is the literal full-triangle integral. The proof consumes
the accepted actual classical count producer and the proved bilateral mass,
not a supplied count, density, or quadrature estimate.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology

theorem gamma5Mass_scalar_budget {c τ ε : ℝ}
    (hc : 0 ≤ c) (hc64 : c ≤ 64) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hτε : τ ≤ ε / 512) :
    (1 + τ) ^ 2 * (c + τ) + τ ≤ c + ε := by
  have hsq : (1 + τ) ^ 2 ≤ 1 + 3 * τ := by
    nlinarith [mul_nonneg hτ (sub_nonneg.mpr hτ1)]
  have hmul := mul_le_mul_of_nonneg_right hsq (add_nonneg hc hτ)
  have hct := mul_le_mul_of_nonneg_right hc64 hτ
  have ht2 := mul_le_mul_of_nonneg_right hτ1 hτ
  nlinarith

/-- Uniform actual scalar upper bound for every rectangular source mask. -/
theorem gamma5Mass_rectangle_count_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ A B C D : ℝ,
      gamma5MassA ≤ A → A ≤ B → B ≤ gamma5ClassicalB →
      gamma5MassA ≤ C → C ≤ D → D ≤ gamma5ClassicalB →
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
        (gamma5MassRectLabels N δ (convolutionWuWindows N Δ V) A B C D) ≤
      (gamma5MassRectangleIntegral A B C D + ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let τ := min 1 (ε / 512)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : τ ≤ ε / 512 := min_le_right _ _
  obtain ⟨TC, hTC4, hcount⟩ := gamma5Classical_mask_upper k hk hδ hδhi hτ hτ
  obtain ⟨TM, hTM4, hmass⟩ := gamma5Mass_rectangle_mass k hk hδ hδhi hτ
  refine ⟨max TC TM, hTC4.trans (le_max_left _ _), ?_⟩
  intro N hNT he i Δ V hb A B C D hA hAB hB hC hCD hD
  have hNC : TC ≤ N := (le_max_left _ _).trans hNT
  have hNM : TM ≤ N := (le_max_right _ _).trans hNT
  have hN2 : 2 ≤ N := by omega
  have htheta := gamma5Mass_theta_nonneg hN2 hδ (by linarith) hb
  have hM := hmass N hNM i Δ V hb A B C D hA hAB hB hC hCD hD
  have hU := hcount N hNC he i Δ V hb
    (gamma5MassRectLabels N δ (convolutionWuWindows N Δ V) A B C D)
    (filter_subset _ _)
  have hI := gamma5Mass_rectangle_bounds hA hAB hB hC hCD hD
  have hbudget := gamma5Mass_scalar_budget hI.1 hI.2 hτ.le hτ1 hτε
  have hmain :
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma5MassRectLabels N δ (convolutionWuWindows N Δ V) A B C D) ≤
        (gamma5MassRectangleIntegral A B C D + τ) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
    linarith [(le_abs_self _).trans hM]
  have hmain' := mul_le_mul_of_nonneg_left hmain (sq_nonneg (1 + τ))
  have hbudget' := mul_le_mul_of_nonneg_right hbudget htheta
  nlinarith

/-- The requested actual full Gamma5 count, with literal C5 and no assumed
arithmetic mass, prime quadrature, density, or sieve estimate. -/
theorem gamma5Mass_full_count_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
        (gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V)) ≤
      (gamma5MassC5 + ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let τ := min 1 (ε / 512)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : τ ≤ ε / 512 := min_le_right _ _
  obtain ⟨TC, hTC4, hcount⟩ := gamma5Classical_full_upper k hk hδ hδhi hτ hτ
  obtain ⟨TM, hTM4, hmass⟩ := gamma5Mass_full_mass k hk hδ hδhi hτ
  refine ⟨max TC TM, hTC4.trans (le_max_left _ _), ?_⟩
  intro N hNT he i Δ V hb
  have hNC : TC ≤ N := (le_max_left _ _).trans hNT
  have hNM : TM ≤ N := (le_max_right _ _).trans hNT
  have hN2 : 2 ≤ N := by omega
  have htheta := gamma5Mass_theta_nonneg hN2 hδ (by linarith) hb
  have hM := hmass N hNM i Δ V hb
  have hU := hcount N hNC he i Δ V hb
  have hbudget := gamma5Mass_scalar_budget gamma5Mass_C5_bounds.1 gamma5Mass_C5_bounds.2
    hτ.le hτ1 hτε
  have hmain :
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V)) ≤
        (gamma5MassC5 + τ) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
    linarith [(le_abs_self _).trans hM]
  have hmain' := mul_le_mul_of_nonneg_left hmain (sq_nonneg (1 + τ))
  have hbudget' := mul_le_mul_of_nonneg_right hbudget htheta
  nlinarith

end Wu2008DoubleSieve
