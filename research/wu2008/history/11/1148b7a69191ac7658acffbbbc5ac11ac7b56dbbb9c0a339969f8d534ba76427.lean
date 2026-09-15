import R2OmegaHighPaid

noncomputable section
namespace WuPaper.R2OmegaHigh
open Wu2008DoubleSieve WuSource.SrcSingle
open Finset Real
open scoped Classical Interval BigOperators

theorem uniform_omega_and_theta {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 4,
      (∑ p ∈ psiPrimes (index j) N, wuOmega1 N p δ (psiTop (index j))) ≤
        2 * wuUpperCoefficient (psiTop (index j)) * theta j N δ +
          ε * truncatedSixthMassScale N ∧
      lowerIntegral j * theta j N δ - ε * truncatedSixthMassScale N ≤
        (∑ p ∈ psiPrimes (index j) N,
          wuOmega2 N p δ (psiNode (index j)) (psiTop (index j))) ∧
      (∑ p ∈ psiPrimes (index j) N,
        wuOmega3 N p δ (psiNode (index j)) (psiTop (index j))) ≤
        (2 / (1 - 2 * δ)) *
          omega3XIntegralEnvelope (psiNode (index j)) (psiTop (index j)) * theta j N δ +
            ε * truncatedSixthMassScale N ∧
      |theta j N δ - 4 * outerIntegral j δ * truncatedSixthMassScale N| ≤
        ε * truncatedSixthMassScale N := by
  obtain ⟨T0, hT04, h0⟩ := omega1_upper hd hh heps
  obtain ⟨T1, _, h1⟩ := omega2_lower hd hh heps
  obtain ⟨T2, _, h2⟩ := omega3_upper hd hh heps
  obtain ⟨T3, _, h3⟩ := theta_integral_error 0 hd hh heps
  obtain ⟨T4, _, h4⟩ := theta_integral_error 1 hd hh heps
  obtain ⟨T5, _, h5⟩ := theta_integral_error 2 hd hh heps
  obtain ⟨T6, _, h6⟩ := theta_integral_error 3 hd hh heps
  refine ⟨max T0 (max T1 (max T2 (max T3 (max T4 (max T5 T6))))),
    hT04.trans (le_max_left _ _), ?_⟩
  intro N hN he j
  refine ⟨h0 N (by omega) he j, h1 N (by omega) he j, h2 N (by omega) he j, ?_⟩
  fin_cases j
  · exact h3 N (by omega) he
  · exact h4 N (by omega) he
  · exact h5 N (by omega) he
  · exact h6 N (by omega) he

theorem proposition44_four_actual {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 4,
      (∑ p ∈ psiPrimes (index j) N,
        (sieveCount N p N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ)) ≤
        (8 * (∫ t in ((1 / 2 - psiRight (index j)) / truncatedSixthLowerAlpha)..psiNode (index j),
          (wuUpperCoefficient t -
            firstFunctionalGainPsiOne (psiNode (index j)) (psiTop (index j))) /
              (t * (1 - 2 * truncatedSixthLowerAlpha * t))) + ε) *
                truncatedSixthMassScale N := by
  obtain ⟨δ, _, _, _, T, hT4, hc⟩ := original_four_windows heps
  exact ⟨T, hT4, fun N hN he j => (hc N hN he j).1.trans (hc N hN he j).2⟩

theorem E02_four_original {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (∑ j : Fin 4, psiCount (index j) N) ≤
        (fourClassical - fourSourceGain + ε) * truncatedSixthMassScale N := by
  obtain ⟨δ, _, _, _, T, hT4, hc⟩ := four_actual_original_gain heps
  exact ⟨T, hT4, fun N hN he => (hc N hN he).1.trans (hc N hN he).2⟩

#check @WuPaper.R2OmegaHigh.uniform_omega_and_theta
#check @WuPaper.R2OmegaHigh.proposition44_four_actual
#check @WuPaper.R2OmegaHigh.E02_four_original
#check @WuPaper.R2OmegaHigh.original_small_delta_four_windows
#check @WuPaper.R2OmegaHigh.actual_four_publications
#check @WuPaper.R2OmegaHigh.four_actual_original_gain
#check @WuPaper.R2OmegaHigh.four_actual_publication_gain
#check @WuPaper.R2OmegaHigh.raw_mother_upper
#check @WuPaper.R2OmegaHigh.fixed_zero_eq_paper
#check @WuPaper.R2OmegaHigh.paper_coefficient_log
#check @WuPaper.R2OmegaHigh.existing_publication_identity
#check @WuPaper.R2OmegaHigh.publication_le_actual
#check @WuPaper.R2OmegaHigh.four_gain_paid
#print axioms WuPaper.R2OmegaHigh.uniform_omega_and_theta
#print axioms WuPaper.R2OmegaHigh.proposition44_four_actual
#print axioms WuPaper.R2OmegaHigh.E02_four_original
#print axioms WuPaper.R2OmegaHigh.original_small_delta_four_windows
#print axioms WuPaper.R2OmegaHigh.actual_four_publications
#print axioms WuPaper.R2OmegaHigh.four_actual_original_gain
#print axioms WuPaper.R2OmegaHigh.four_actual_publication_gain
#print axioms WuPaper.R2OmegaHigh.raw_mother_upper
#print axioms WuPaper.R2OmegaHigh.fixed_zero_eq_paper
#print axioms WuPaper.R2OmegaHigh.paper_coefficient_log
#print axioms WuPaper.R2OmegaHigh.existing_publication_identity
#print axioms WuPaper.R2OmegaHigh.publication_le_actual
#print axioms WuPaper.R2OmegaHigh.four_gain_paid
end WuPaper.R2OmegaHigh
