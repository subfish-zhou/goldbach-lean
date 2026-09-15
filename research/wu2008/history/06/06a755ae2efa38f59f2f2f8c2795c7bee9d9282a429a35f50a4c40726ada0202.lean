import R2OmegaHighLimit

noncomputable section
namespace WuPaper.R2OmegaHigh
open Wu2008DoubleSieve WuSource.SrcSingle
open Finset Real
open scoped Classical Interval BigOperators

def publicationCoefficient (j : Fin 4) : ℝ :=
  8 * (1 - Wu04FirstCore.publication j.castSucc) * psiLogWeight (index j)
def fourClassical : ℝ := 8 * ∑ j : Fin 4, psiLogWeight (index j)
def fourSourceGain : ℝ :=
  8 * ∑ j : Fin 4, psiLogWeight (index j) *
    firstFunctionalGainPsiOne (psiNode (index j)) (psiTop (index j))
def fourPaidGain : ℝ :=
  8 * ∑ j : Fin 4, psiLogWeight (index j) * Wu04FirstCore.publication j.castSucc

theorem existing_publication_identity (j : Fin 4) :
    psiPublication (index j) = Wu04FirstCore.publication j.castSucc := by
  simp only [index, psiPublication, Fin.addCases_right]

theorem publication_le_original (j : Fin 4) :
    Wu04FirstCore.publication j.castSucc ≤
      firstFunctionalGainPsiOne (psiNode (index j)) (psiTop (index j)) := by
  have hr := seven_source_rows.2 j
  change psiNode (index j) = _ ∧ psiTop (index j) = _ at hr
  rw [hr.1, hr.2]
  linarith only [Wu04FirstPaid.publication_with_slack j, Wu04FirstPaid.slack_pos j]

theorem publication_le_actual (j : Fin 4) {δ : ℝ} (hd : 0 < δ)
    (hr : δ ≤ Wu04FirstPaid.commonRadius) :
    Wu04FirstCore.publication j.castSucc ≤
      firstFunctionalGainPsi δ (psiNode (index j)) (psiTop (index j)) := by
  have hs := seven_source_rows.2 j
  change psiNode (index j) = _ ∧ psiTop (index j) = _ at hs
  rw [hs.1, hs.2]
  exact first_forcing_paid j hd (hr.trans (Wu04FirstPaid.commonRadius_le j))

theorem paper_coefficient_le_publication (j : Fin 4) :
    paperCoefficient j ≤ publicationCoefficient j := by
  rw [paper_coefficient_log, publicationCoefficient]
  gcongr
  · exact seven_log_weights_nonneg (index j)
  · exact publication_le_original j

theorem four_gain_paid : fourPaidGain ≤ fourSourceGain := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  exact sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left (publication_le_original j) (seven_log_weights_nonneg (index j)))

theorem sum_paper_coefficient :
    (∑ j : Fin 4, paperCoefficient j) = fourClassical - fourSourceGain := by
  calc
    _ = ∑ j : Fin 4, 8 * (psiLogWeight (index j) - psiLogWeight (index j) *
        firstFunctionalGainPsiOne (psiNode (index j)) (psiTop (index j))) := by
      apply sum_congr rfl
      intro j _
      rw [paper_coefficient_log]
      ring
    _ = _ := by rw [← mul_sum, sum_sub_distrib, mul_sub]; rfl

theorem sum_publication_coefficient :
    (∑ j : Fin 4, publicationCoefficient j) = fourClassical - fourPaidGain := by
  calc
    _ = ∑ j : Fin 4, 8 * (psiLogWeight (index j) -
        psiLogWeight (index j) * Wu04FirstCore.publication j.castSucc) := by
      apply sum_congr rfl
      intro j _
      unfold publicationCoefficient
      ring
    _ = _ := by rw [← mul_sum, sum_sub_distrib, mul_sub]; rfl

theorem original_small_delta_four_windows {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 4,
        psiCount (index j) N ≤ sevenRawSource N δ (index j) ∧
        sevenRawSource N δ (index j) ≤
          (paperCoefficient j + ε) * truncatedSixthMassScale N := by
  obtain ⟨r, hr, hr1, hc⟩ := common_coefficient_radius (half_pos heps)
  refine ⟨r, hr, hr1, ?_⟩
  intro δ hd hdr
  have hh : δ ≤ 1 / 100 := hdr.le.trans hr1
  obtain ⟨T0, hT04, h0⟩ := raw_fixed_integral_upper 0 hd hh (half_pos heps)
  obtain ⟨T1, _, h1⟩ := raw_fixed_integral_upper 1 hd hh (half_pos heps)
  obtain ⟨T2, _, h2⟩ := raw_fixed_integral_upper 2 hd hh (half_pos heps)
  obtain ⟨T3, _, h3⟩ := raw_fixed_integral_upper 3 hd hh (half_pos heps)
  refine ⟨max T0 (max T1 (max T2 T3)), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven j
  have hN2 : 2 ≤ N := by omega
  have hf : sevenRawSource N δ (index j) ≤
      (fixedCoefficient j δ + ε / 2) * truncatedSixthMassScale N := by
    fin_cases j
    · exact h0 N (by omega) hEven
    · exact h1 N (by omega) hEven
    · exact h2 N (by omega) hEven
    · exact h3 N (by omega) hEven
  refine ⟨seven_raw_source_count hN2 hd hh (index j), hf.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (scale_nonneg hN2)
  have h := (abs_lt.mp (hc δ hd hdr j)).2
  linarith only [h]

theorem actual_four_publications {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 4,
      psiCount (index j) N ≤
        (publicationCoefficient j + ε) * truncatedSixthMassScale N := by
  obtain ⟨δ, _, _, _, T, hT4, hc⟩ := original_four_windows heps
  refine ⟨T, hT4, ?_⟩
  intro N hN he j
  exact ((hc N hN he j).1.trans (hc N hN he j).2).trans
    (mul_le_mul_of_nonneg_right (add_le_add (paper_coefficient_le_publication j) le_rfl)
      (scale_nonneg (by omega)))

theorem four_actual_original_gain {ε : ℝ} (heps : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 100 ∧ δ ≤ Wu04FirstPaid.commonRadius ∧
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (∑ j : Fin 4, psiCount (index j) N) ≤ (∑ j : Fin 4, sevenRawSource N δ (index j)) ∧
        (∑ j : Fin 4, sevenRawSource N δ (index j)) ≤
          (fourClassical - fourSourceGain + ε) * truncatedSixthMassScale N := by
  obtain ⟨δ, hd, hh, hr, T, hT4, hc⟩ := original_four_windows (show 0 < ε / 4 by positivity)
  refine ⟨δ, hd, hh, hr, T, hT4, ?_⟩
  intro N hN he
  refine ⟨sum_le_sum (fun j _ => (hc N hN he j).1), ?_⟩
  have hsum := sum_le_sum (s := univ) (fun j _ => (hc N hN he j).2)
  rw [← sum_mul, sum_add_distrib, sum_paper_coefficient] at hsum
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    show (4 : ℝ) * (ε / 4) = ε by ring] using hsum

theorem four_actual_publication_gain {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (∑ j : Fin 4, psiCount (index j) N) ≤
        (fourClassical - fourPaidGain + ε) * truncatedSixthMassScale N := by
  obtain ⟨δ, _, _, _, T, hT4, hc⟩ := four_actual_original_gain heps
  refine ⟨T, hT4, ?_⟩
  intro N hN he
  apply ((hc N hN he).1.trans (hc N hN he).2).trans
  apply mul_le_mul_of_nonneg_right _ (scale_nonneg (by omega))
  linarith only [four_gain_paid]

#check @WuPaper.R2OmegaHigh.publicationCoefficient
#check @WuPaper.R2OmegaHigh.fourClassical
#check @WuPaper.R2OmegaHigh.fourSourceGain
#check @WuPaper.R2OmegaHigh.fourPaidGain
#check @WuPaper.R2OmegaHigh.existing_publication_identity
#check @WuPaper.R2OmegaHigh.publication_le_original
#check @WuPaper.R2OmegaHigh.publication_le_actual
#check @WuPaper.R2OmegaHigh.paper_coefficient_le_publication
#check @WuPaper.R2OmegaHigh.four_gain_paid
#check @WuPaper.R2OmegaHigh.sum_paper_coefficient
#check @WuPaper.R2OmegaHigh.sum_publication_coefficient
#check @WuPaper.R2OmegaHigh.original_small_delta_four_windows
#check @WuPaper.R2OmegaHigh.actual_four_publications
#check @WuPaper.R2OmegaHigh.four_actual_original_gain
#check @WuPaper.R2OmegaHigh.four_actual_publication_gain
#print axioms WuPaper.R2OmegaHigh.publicationCoefficient
#print axioms WuPaper.R2OmegaHigh.fourClassical
#print axioms WuPaper.R2OmegaHigh.fourSourceGain
#print axioms WuPaper.R2OmegaHigh.fourPaidGain
#print axioms WuPaper.R2OmegaHigh.existing_publication_identity
#print axioms WuPaper.R2OmegaHigh.publication_le_original
#print axioms WuPaper.R2OmegaHigh.publication_le_actual
#print axioms WuPaper.R2OmegaHigh.paper_coefficient_le_publication
#print axioms WuPaper.R2OmegaHigh.four_gain_paid
#print axioms WuPaper.R2OmegaHigh.sum_paper_coefficient
#print axioms WuPaper.R2OmegaHigh.sum_publication_coefficient
#print axioms WuPaper.R2OmegaHigh.original_small_delta_four_windows
#print axioms WuPaper.R2OmegaHigh.actual_four_publications
#print axioms WuPaper.R2OmegaHigh.four_actual_original_gain
#print axioms WuPaper.R2OmegaHigh.four_actual_publication_gain
end WuPaper.R2OmegaHigh
