import W06Decomposition

noncomputable section
namespace WuTarget.W06
open Real Wu2008DoubleSieve NodeExtension ActualNineFeedback
open scoped BigOperators

theorem first_multipliers (i : Fin 5) :
    0 < eCoefficient (firstS i) ∧
      0 ≤ jCoefficient (firstNode i) (firstS i)/2 := by
  have hg := first_geometry i
  have hS : firstS i < 5 := by fin_cases i <;> norm_num [firstS]
  exact ⟨eCoefficient_pos hg.2.2.1 hS,
    div_nonneg (jCoefficient_nonneg hg.1 (hg.2.1.trans hg.2.2.1)) (by norm_num)⟩

theorem first_J_multiplier_pos (i : Fin 5) (hi : i ≠ 4) :
    0 < jCoefficient (firstNode i) (firstS i)/2 := by
  have hsS : firstNode i < firstS i := by
    fin_cases i <;> norm_num [firstNode, firstS] at hi ⊢
    exact hi rfl
  exact div_pos (jCoefficient_pos (first_geometry i).1 hsS) (by norm_num)

theorem terminal_J_multiplier : jCoefficient (firstNode 4) (firstS 4)/2 = 0 := by
  change jCoefficient ((26+4)/10) 3/2 = 0
  norm_num [jCoefficient]

theorem coupled_multipliers (i : Fin 4) :
    0 < 4*eCoefficient (coupledRow i).S/5 ∧
    0 < eCoefficient (coupledRow i).kappa1/5 ∧
    0 < jCoefficient (coupledRow i).s (coupledRow i).S/5 ∧
    0 < jCoefficient (coupledRow i).kappa2 (coupledRow i).S/5 ∧
    0 < jCoefficient (coupledRow i).kappa3 (coupledRow i).S/5 := by
  have hp := coupledRow_geometry i
  have hg := coupled_geometry_bounds hp
  have hm := hp.1.mother
  have hS : (coupledRow i).S < 5 := by
    fin_cases i <;> norm_num [coupledRow, SecondFunctionalPositive.parameters,
      SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
      SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]
  have h2 := hm.kappa2_lt_kappa1.trans_le hm.kappa1_le_S
  have h3 := hm.kappa3_lt_kappa2.trans h2
  have hs := hm.s_le_kappa3.trans_lt h3
  exact ⟨div_pos (mul_pos (by norm_num) (eCoefficient_pos hp.1.three_le_S hS))
      (by norm_num),
    div_pos (eCoefficient_pos hp.2.1 (hm.kappa1_le_S.trans_lt hS)) (by norm_num),
    div_pos (jCoefficient_pos hg.1 hs) (by norm_num),
    div_pos (jCoefficient_pos hg.2.2.1 h2) (by norm_num),
    div_pos (jCoefficient_pos hg.2.2.2.2.1 h3) (by norm_num)⟩

theorem first_row_coefficient_pos (i : Fin 5) :
    0 < firstCoefficient (firstNode i) (firstS i) :=
  add_pos_of_pos_of_nonneg (first_multipliers i).1 (first_multipliers i).2

theorem coupled_row_coefficient_pos (i : Fin 4) :
    0 < coupledCoefficient (coupledRow i) := by
  obtain ⟨h0, h1, hj0, hj2, hj3⟩ := coupled_multipliers i
  unfold coupledCoefficient
  linarith only [h0, h1, hj0, hj2, hj3]

def rowCoefficient (i : Fin 9) : ℝ :=
  if h : i.val < 4 then coupledCoefficient (coupledRow ⟨i.val, h⟩)
  else firstCoefficient (firstNode ⟨i.val-4, by omega⟩)
    (firstS ⟨i.val-4, by omega⟩)

def rowRemainder (z : Fin 9 → ℝ) (i : Fin 9) : ℝ :=
  if h : i.val < 4 then coupledRemainder (coupledRow ⟨i.val, h⟩) z
  else firstRemainder z (firstNode ⟨i.val-4, by omega⟩)
    (firstS ⟨i.val-4, by omega⟩)

theorem rowCoefficient_pos (i : Fin 9) : 0 < rowCoefficient i := by
  unfold rowCoefficient
  split_ifs
  · exact coupled_row_coefficient_pos _
  · exact first_row_coefficient_pos _

theorem rowRemainder_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) (i : Fin 9) :
    0 ≤ rowRemainder z i := by
  unfold rowRemainder
  split_ifs
  · exact coupledRemainder_nonneg (coupledRow_geometry _) hz
  · have hg := first_geometry (⟨i.val-4, by omega⟩ : Fin 5)
    exact firstRemainder_nonneg hz hg.1 hg.2.2.1 hg.2.2.2.1
      (hg.2.1.trans hg.2.2.1) hg.2.2.2.2

theorem feedback_split (z : Fin 9 → ℝ) (i : Fin 9) :
    feedback z i = rowCoefficient i * aProfile (nineProfile z) + rowRemainder z i := by
  unfold feedback rowCoefficient rowRemainder
  split_ifs
  · exact coupledFeedback_split (coupledRow_geometry _) z
  · have hg := first_geometry (⟨i.val-4, by omega⟩ : Fin 5)
    exact firstFeedback_split z hg.1 hg.2.2.1 hg.2.2.2.1
      (hg.2.1.trans hg.2.2.1) hg.2.2.2.2

theorem feedback_sigma_lower {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) (i : Fin 9) :
    rowCoefficient i * sigmaLower z + rowRemainder z i ≤ feedback z i := by
  rw [feedback_split]
  exact add_le_add (mul_le_mul_of_nonneg_left (sigmaLower_le_aProfile hz)
    (rowCoefficient_pos i).le) le_rfl

def sigmaMatrix (i k : Fin 9) : ℝ := rowCoefficient i * sigmaCoeff k

def nonSigmaMatrix (i k : Fin 9) : ℝ := rowRemainder (nodeBasis k) i

theorem sigmaMatrix_pos (i k : Fin 9) : 0 < sigmaMatrix i k :=
  mul_pos (rowCoefficient_pos i) (sigmaCoeff_pos k)

theorem nonSigmaMatrix_nonneg (i k : Fin 9) : 0 ≤ nonSigmaMatrix i k :=
  rowRemainder_nonneg (nodeBasis_nonneg k) i

theorem sigmaMatrix_apply (z : Fin 9 → ℝ) (i : Fin 9) :
    (∑ k, sigmaMatrix i k * z k) = rowCoefficient i * sigmaLower z := by
  unfold sigmaMatrix sigmaLower
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem nonSigmaMatrix_apply (z : Fin 9 → ℝ) (i : Fin 9) :
    (∑ k, nonSigmaMatrix i k * z k) = rowRemainder z i := by
  have he := feedback_expansion z i
  simp only [feedbackMatrix, feedback_split] at he
  rw [aProfile_expansion z] at he
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc] at he
  rw [Finset.mul_sum] at he
  have hm : (∑ k, rowCoefficient i * (z k * aProfile (nineProfile (nodeBasis k)))) =
      ∑ k, rowCoefficient i * (aProfile (nineProfile (nodeBasis k)) * z k) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hm] at he
  unfold nonSigmaMatrix
  linarith only [he]

theorem feedbackMatrix_split (i k : Fin 9) :
    feedbackMatrix i k =
      rowCoefficient i * aProfile (nineProfile (nodeBasis k)) + nonSigmaMatrix i k :=
  feedback_split (nodeBasis k) i

theorem sigmaMatrix_add_nonSigma_le (i k : Fin 9) :
    sigmaMatrix i k + nonSigmaMatrix i k ≤ feedbackMatrix i k := by
  have h := feedback_sigma_lower (nodeBasis_nonneg k) i
  rw [sigmaLower_basis] at h
  exact h

theorem sigmaMatrix_le_feedbackMatrix (i k : Fin 9) :
    sigmaMatrix i k ≤ feedbackMatrix i k :=
  (le_add_of_nonneg_right (nonSigmaMatrix_nonneg i k)).trans (sigmaMatrix_add_nonSigma_le i k)

theorem add_nonSigma_payment {B : Fin 9 → Fin 9 → ℝ}
    (hB : ∀ i k, B i k ≤ nonSigmaMatrix i k) (i k : Fin 9) :
    sigmaMatrix i k + B i k ≤ feedbackMatrix i k :=
  (add_le_add le_rfl (hB i k)).trans (sigmaMatrix_add_nonSigma_le i k)

theorem actual_sigma_feedback {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10) (i : Fin 9) :
    base i - deltaLoss δ * loss i +
      (∑ k, sigmaMatrix i k * actualNine δ k) + rowRemainder (actualNine δ) i ≤
        actualNine δ i := by
  have hp := feedback_sigma_lower (actualNine_nonneg hd hh) i
  have ha := actual_feedback hd hh i
  rw [sigmaMatrix_apply]
  linarith only [hp, ha]

theorem actual_sigma_matrix_feedback {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/10)
    (i : Fin 9) :
    base i - deltaLoss δ * loss i +
      (∑ k, (sigmaMatrix i k + nonSigmaMatrix i k) * actualNine δ k) ≤
        actualNine δ i := by
  simp only [add_mul, Finset.sum_add_distrib, nonSigmaMatrix_apply]
  have h := actual_sigma_feedback hd hh i
  linarith only [h]

end WuTarget.W06
