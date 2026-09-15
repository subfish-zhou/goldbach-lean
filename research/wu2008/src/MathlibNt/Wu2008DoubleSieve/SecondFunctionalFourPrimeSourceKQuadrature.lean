import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeSourceKMasses

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset Real Filter FourPrimeContinuous
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The actual mother parameters lie in the fixed compact quadrature region. -/
theorem sourceK_compact {p : SecondFunctionalParameters}
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    CompactParameters (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) := by
  have h2 : 0 < p.kappa2 := by linarith [hp.s_le_kappa3, hp.kappa3_lt_kappa2]
  have h1 : 0 < p.kappa1 := lt_trans h2 hp.kappa2_lt_kappa1
  obtain ⟨_, h23, h3s, hs2⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  exact ⟨one_div_le_one_div_of_le h1 (hp.kappa1_le_S.trans hp.S_le_ten),
    one_div_le_one_div_of_le h2 hp.kappa2_lt_kappa1.le, h23, h3s, hs2⟩

/-- One threshold precedes all scales, boxes, mother parameters and word labels. -/
theorem sourceClosedK_uniform (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), ∀ j : Fin 4,
        |sourceClosedK N d δ p j - sourceLegalK N d δ p j| < epsilon := by
  let Phi := max 2 (1 / wuLocalExponent k δ)
  obtain ⟨R0, _, hR0⟩ := closedPrimeK_four_uniform Phi (le_max_left _ _) epsilon he
  have heta := wuLocalExponent_pos k hδ hδhi
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb p hp hs d hd
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hg := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
  have hphi : 2 ≤ omega3XPhi N d δ := by
    have hgap : 0 < 2 * δ / (1/2-δ) := by positivity
    linarith [hg.2.2.1]
  have hlarge := (hT N ((le_max_right _ _).trans hN)).trans hg.1
  have h := hR0 _ hlarge _ ⟨hphi, hg.2.2.2.trans (le_max_right _ _)⟩
    _ _ _ _ (sourceK_compact hp hs)
  simpa only [sourceClosedK, sourceLegalK, closedK, legalK, vec,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true, Fin.cases_zero,
    Fin.cases_succ] using h

/-- Four individual errors receive one common budget, rather than four budgets. -/
theorem four_abs_budget {a b : Fin 4 → ℝ} {epsilon : ℝ}
    (h : ∀ j, |a j - b j| < epsilon / 4) :
    (∑ j, |a j - b j|) < epsilon := by
  calc
    _ < ∑ _j : Fin 4, epsilon / 4 :=
      sum_lt_sum_of_nonempty (by simp) (fun j _ => h j)
    _ = epsilon := by simp; ring

/-- The same actual phi and threshold serve every word and their total error. -/
theorem sourceClosedK_four_uniform (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (∀ j : Fin 4, |sourceClosedK N d δ p j - sourceLegalK N d δ p j| < epsilon) ∧
        (∑ j : Fin 4, |sourceClosedK N d δ p j - sourceLegalK N d δ p j|) < epsilon ∧
        |(∑ j : Fin 4, sourceClosedK N d δ p j) -
          (∑ j : Fin 4, sourceLegalK N d δ p j)| < epsilon := by
  obtain ⟨T, hT4, hT⟩ := sourceClosedK_uniform k hδ hδhi
    (show 0 < epsilon/4 by positivity)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs d hd
  have h := hT N hN i Δ V hb p hp hs d hd
  have hsum := four_abs_budget h
  refine ⟨fun j => (h j).trans_le (by linarith), hsum, ?_⟩
  rw [← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans_lt hsum

end Wu2008DoubleSieve.FourPrimeNonunit

