import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSourceLogCap

namespace Wu2008DoubleSieve.HighUnitSource
open HighUnit

/-- The actual unfiltered cardinal mass, not a source upper bound, obeys the log cap.
No sieve density is used here and the unchanged error is not a Theta error. -/
theorem boxed_mass_pair_log_cap (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ a2 a b : ℝ, 1/10 ≤ a2 → a2 ≤ a → a ≤ b → b ≤ 1/2 →
      let W := convolutionWuWindows N Δ V
      boxedSigma20 N δ W (fun _ => a2) (fun _ => a) (fun _ => b) +
        boxedSigma21 N δ W (fun _ => a) (fun _ => b) ≤
      (unitLogCap20 a2 a b + unitLogCap21 a b) * unitLogMass N δ W +
        epsilon * ((N : ℝ) / Real.log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T,hT4,hT⟩ := boxed_sigma_pair_combined k hδ hδhi he
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hbox a2 a b ha haa hab hb
  have hc := boxed_integral_pair_log_cap (by omega) hδ hδhi hbox ha haa hab hb
  have hu := (hT N hN i Δ V hbox (fun _ => a2) (fun _ => a) (fun _ => b)
    (fun _ _ => ⟨ha,ha.trans haa,hb⟩)).2.2
  dsimp only at hc hu ⊢
  have hu' := (abs_le.mp hu).2
  linarith

/-- The mother parameters are quantified after the common threshold and source box. -/
theorem mother_boxed_mass_pair_log_cap (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      boxedSigma20 N δ W (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
        boxedSigma21 N δ W (fun _ => 1/p.kappa3) (fun _ => 1/p.s) ≤
      (unitLogCap20 (1/p.kappa2) (1/p.kappa3) (1/p.s) +
        unitLogCap21 (1/p.kappa3) (1/p.s)) * unitLogMass N δ W +
        epsilon * ((N : ℝ) / Real.log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T,hT4,hT⟩ := boxed_mass_pair_log_cap k hδ hδhi he
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hbox p hp hs
  obtain ⟨ha,haa,hab,hb⟩ := parameter_log_cap_bounds hp hs
  exact hT N hN i Δ V hbox _ _ _ ha haa hab hb

end Wu2008DoubleSieve.HighUnitSource
