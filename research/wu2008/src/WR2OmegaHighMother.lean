import WR2OmegaHighLower
import WR2OmegaHighSwitched

noncomputable section
namespace WuPaper.R2OmegaHigh
open Wu2008DoubleSieve WuSource.SrcSingle
open Finset Real
open scoped Classical Interval BigOperators

theorem psi_coefficient (j : Fin 4) (δ : ℝ) :
    wuUpperCoefficient (psiTop (index j)) - lowerIntegral j / 2 +
      omega3XIntegralEnvelope (psiNode (index j)) (psiTop (index j)) / (1 - 2 * δ) =
        1 - firstFunctionalGainPsi δ (psiNode (index j)) (psiTop (index j)) := by
  have hg := geometry j
  have hA : wuUpperCoefficient (psiNode (index j)) = 1 := by
    unfold wuUpperCoefficient
    rw [MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965F_eq_of_le_three hg.2.1]
    field_simp [(show psiNode (index j) ≠ 0 by linarith [hg.1]),
      (exp_pos eulerMascheroniConstant).ne']
  unfold firstFunctionalGainPsi
  rw [hA]
  change _ = 1 - (1 - wuUpperCoefficient (psiTop (index j)) +
    (1 / 2) * lowerIntegral j -
    omega3XIntegralEnvelope (psiNode (index j)) (psiTop (index j)) / (1 - 2 * δ))
  ring

theorem raw_mother_upper {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 4,
      sevenRawSource N δ (index j) ≤
        (1 - firstFunctionalGainPsi δ (psiNode (index j)) (psiTop (index j))) * theta j N δ +
          ε * truncatedSixthMassScale N := by
  have he : 0 < 2 * ε / 3 := by positivity
  obtain ⟨T0, hT04, h0⟩ := omega1_upper hd hh he
  obtain ⟨T1, _, h1⟩ := omega2_lower hd hh he
  obtain ⟨T2, _, h2⟩ := omega3_upper hd hh he
  refine ⟨max T0 (max T1 T2), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven j
  have ha := h0 N (by omega) hEven j
  have hb := h1 N (by omega) hEven j
  have hc := h2 N (by omega) hEven j
  simp only [index, sevenRawSource, Fin.addCases_right]
  change (∑ p ∈ psiPrimes (index j) N,
    (wuOmega1 N p δ (psiTop (index j)) -
      wuOmega2 N p δ (psiNode (index j)) (psiTop (index j)) +
      wuOmega3 N p δ (psiNode (index j)) (psiTop (index j)))) / 2 ≤
    (1 - firstFunctionalGainPsi δ (psiNode (index j)) (psiTop (index j))) * theta j N δ +
      ε * truncatedSixthMassScale N
  rw [← psi_coefficient j δ, sum_add_distrib, sum_sub_distrib]
  ring_nf at ha hb hc ⊢
  linarith only [ha, hb, hc]

theorem actual_psi_theta_upper {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 4,
      psiCount (index j) N ≤
        (1 - firstFunctionalGainPsi δ (psiNode (index j)) (psiTop (index j))) * theta j N δ +
          ε * truncatedSixthMassScale N := by
  obtain ⟨T, hT4, hT⟩ := raw_mother_upper hd hh heps
  exact ⟨T, hT4, fun N hN he j =>
    (seven_raw_source_count (show 2 ≤ N by omega) hd hh (index j)).trans (hT N hN he j)⟩

#check @WuPaper.R2OmegaHigh.psi_coefficient
#check @WuPaper.R2OmegaHigh.raw_mother_upper
#check @WuPaper.R2OmegaHigh.actual_psi_theta_upper
#print axioms WuPaper.R2OmegaHigh.psi_coefficient
#print axioms WuPaper.R2OmegaHigh.raw_mother_upper
#print axioms WuPaper.R2OmegaHigh.actual_psi_theta_upper
end WuPaper.R2OmegaHigh
