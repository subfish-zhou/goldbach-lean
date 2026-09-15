import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairClassicalPorts

namespace Wu2008DoubleSieve.MotherPair
open Finset Real
open scoped Classical

/-- The complement mask needed by a later H-gain assembly is retained. -/
theorem classical_term_mask_upper (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (k : ℕ) (hk : 1≤k) {δ η ε : ℝ} (hδ : 0<δ) (hδhi : δ≤1/10)
    (hη : 0<η) (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N, T≤N → Even N → ∀ i Δ V, wuSourceBox k δ N i Δ V →
      ∀ j : Term, ∀ X : Finset Gamma5ClassicalLabel,
      X ⊆ termLabels p j N δ (convolutionWuWindows N Δ V) →
      termCount p j N δ (convolutionWuWindows N Δ V) X ≤
        (1+η)^2*gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X +
          ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,h⟩ := classical_mask_upper (classical_cap hp) k hk hδ hδhi hη hε
  refine ⟨T,hT,?_⟩
  intro N hN he i Δ V hb j X hX
  have hN2 : 2≤N := by omega
  have hs := hX.trans (termLabels_subset_cap hp j hN2 hδ (by linarith) hb)
  exact (termCount_le_fixedCount p j N δ _ _ X hs).trans (h N hN he i Δ V hb X hs)

theorem classical_slack_budget {η ε K C : ℝ}
    (hη : 0<η) (hη1 : η≤1) (hε : 0<ε) (hC : 0≤C) (hCK : C≤K)
    (hpay : 6*η*(K+1)≤ε) :
    (1+η)^2*(C+ε/16)+ε/4 ≤ C+ε := by
  have h1 : 0≤3*η-((1+η)^2-1) := by nlinarith
  have h2 : 0≤4-(1+η)^2 := by nlinarith
  nlinarith [mul_nonneg h1 hC, mul_nonneg h2 hε.le,
    mul_nonneg hη.le (sub_nonneg.mpr hCK)]

/-- Classical integral upper bound for each original mother term.
No H gain is discarded from any existing improved theorem: this is a separate
classical endpoint, and the arbitrary-mask producer above remains available. -/
theorem classical_original_upper (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (k : ℕ) (hk : 1≤k) {δ ε : ℝ} (hδ : 0<δ) (hδhi : δ≤1/10) (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N, T≤N → Even N → ∀ i Δ V, wuSourceBox k δ N i Δ V →
      ∀ j : Term, secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) j.index ≤
        (classicalIntegral p j+ε)*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let K : ℝ := 16*(1/(1-2*(1/p.kappa3)))
  have hg : 0<1-2*(1/p.kappa3) := by linarith [(classical_cap hp).cap_lt_half]
  have hK : 0<K := by dsimp [K]; positivity
  let η : ℝ := min 1 (ε/(6*(K+1)))
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hpay : 6*η*(K+1)≤ε := by
    have h := (le_div_iff₀ (show 0<6*(K+1) by positivity)).mp (min_le_right 1 (ε/(6*(K+1))))
    dsimp [η]
    nlinarith
  obtain ⟨TC,hTC,hC⟩ := classical_term_mask_upper p hp k hk hδ hδhi hη
    (show 0<ε/4 by positivity)
  obtain ⟨TM,hTM,hM⟩ := term_mass p hp k hδ hδhi (show 0<ε/16 by positivity)
  refine ⟨max TC TM,hTC.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb j
  have hNC : TC≤N := (le_max_left _ _).trans hN
  have hNM : TM≤N := (le_max_right _ _).trans hN
  have hN2 : 2≤N := by omega
  have hcount := hC N hNC he i Δ V hb j _ (Subset.refl _)
  have hmass := hM N hNM i Δ V hb j
  have hθ := gamma5Mass_theta_nonneg hN2 hδ (by linarith) hb
  have hI := classicalIntegral_bounds hp j
  have hbudget := classical_slack_budget hη hη1 hε hI.1 hI.2 hpay
  rw [← termCount_eq_original p hp j hN2 hδ (by linarith) hb]
  apply hcount.trans
  calc
    _ ≤ (1+η)^2*((classicalIntegral p j+ε/16)*
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) +
        ε/4*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have h := (abs_le.mp hmass).2
      linarith
    _ = ((1+η)^2*(classicalIntegral p j+ε/16)+ε/4)*
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hθ

/-- Four original counts together, with one total error budget. -/
theorem classical_four_original_upper (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (k : ℕ) (hk : 1≤k) {δ ε : ℝ} (hδ : 0<δ) (hδhi : δ≤1/10) (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N, T≤N → Even N → ∀ i Δ V, wuSourceBox k δ N i Δ V →
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 5 +
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 6 +
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 7 +
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 8 ≤
      (classicalIntegral p .gammaFive+classicalIntegral p .gammaSix+
        classicalIntegral p .gammaSeven+classicalIntegral p .gammaEight+ε)*
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,h⟩ := classical_original_upper p hp k hk hδ hδhi (show 0<ε/4 by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN he i Δ V hb
  have h5 := h N hN he i Δ V hb .gammaFive
  have h6 := h N hN he i Δ V hb .gammaSix
  have h7 := h N hN he i Δ V hb .gammaSeven
  have h8 := h N hN he i Δ V hb .gammaEight
  simp only [Term.index] at h5 h6 h7 h8
  linarith only [h5,h6,h7,h8]

end Wu2008DoubleSieve.MotherPair
