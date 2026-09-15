import Hf4ContinueDensity

noncomputable section
namespace Hf4Continue
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment
open Wu04WholeCollection ActualNineFeedback
open scoped Interval BigOperators

theorem newCellPayment_pos {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    0 < newCellPayment a b := by
  rw [← newDensity_integral ha hab.le]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    (newDensity_continuous ha hab.le).intervalIntegrable
    (fun t ht => newDensity_pos (ha.trans_lt ht.1)) hab

/-- Only the unchanged original cells and weights are used. -/
def newVariation (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9, z k*newCellPayment (upperLeft k) (upperNode k)

theorem newVariation_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) : 0 ≤ newVariation z := by
  apply Finset.sum_nonneg
  intro k _
  obtain ⟨ha,hab,_⟩ := SigmaEndpointPayment.original_cell_bounds k
  exact mul_nonneg (hz k) (newCellPayment_nonneg ha hab)

theorem newVariation_pos : 0 < newVariation NineFeedbackStrength.originalH := by
  apply Finset.sum_pos'
  · intro k _
    obtain ⟨ha,hab,_⟩ := SigmaEndpointPayment.original_cell_bounds k
    exact mul_nonneg (CoupledIntegralRecovery.originalH_nonneg k) (newCellPayment_nonneg ha hab)
  · obtain ⟨k,hk⟩ := Hf4Next.original_has_positive_weight
    exact ⟨k,Finset.mem_univ k,mul_pos hk
      (newCellPayment_pos (SigmaEndpointPayment.original_cell_bounds k).1
        (Hf4Next.original_cell_strict k))⟩

theorem newVariation_integral (z : Fin 9 → ℝ) :
    newVariation z = ∫ t in (1:ℝ)..3, nineProfile z t*newDensity t := by
  rw [profile_integral_cells z le_rfl (by norm_num [upperNode])
    (newDensity_continuous (by norm_num) (by norm_num))]
  unfold newVariation
  apply Finset.sum_congr rfl
  intro k _
  have he : cellLeft 1 k = upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he]
  obtain ⟨ha,hab,_⟩ := SigmaEndpointPayment.original_cell_bounds k
  rw [newDensity_integral ha hab]

/-- Actual original numerator comparison before any denominator weakening. -/
theorem full_numerator_add_new_le :
    SigmaVariableFull.numerator NineFeedbackStrength.originalH+
      newVariation NineFeedbackStrength.originalH ≤
        ∫ t in (1:ℝ)..3, nineProfile NineFeedbackStrength.originalH t/t*sigma 3 (t+2) (t+1) := by
  have hp := nineProfile_integrable NineFeedbackStrength.originalH
  have hi := hp.mul_continuousOn SigmaVariableFull.weight_continuous
  have hj := hp.mul_continuousOn (newDensity_continuous (by norm_num) (by norm_num))
  rw [SigmaVariableFull.numerator_integral, newVariation_integral, ← intervalIntegral.integral_add hi hj]
  apply intervalIntegral.integral_mono_on (by norm_num) (hi.add hj)
    ((profile_div_integrable hp).mul_continuousOn original_sigma_continuous)
  intro t ht
  have h := mul_le_mul_of_nonneg_left (full_weight_add_new_le ht)
    (nineProfile_nonneg CoupledIntegralRecovery.originalH_nonneg t)
  calc
    _ = nineProfile NineFeedbackStrength.originalH t*(SigmaVariableFull.weight t+newDensity t) := by ring
    _ ≤ nineProfile NineFeedbackStrength.originalH t*(sigma 3 (t+2) (t+1)/t) := h
    _ = _ := by ring

theorem full_profile_add_new_le_actual :
    (SigmaVariableFull.numerator NineFeedbackStrength.originalH+newVariation NineFeedbackStrength.originalH)/
      (1-D0FullDensity.finiteD) ≤ aProfile (nineProfile NineFeedbackStrength.originalH) := by
  have hn : 0 ≤ SigmaVariableFull.numerator NineFeedbackStrength.originalH :=
    SigmaInnerProfile.original_numerator_pos.le.trans
      (SigmaVariableFull.old_numerator_le CoupledIntegralRecovery.originalH_nonneg)
  have hn' := add_nonneg hn (newVariation_nonneg CoupledIntegralRecovery.originalH_nonneg)
  calc
    _ ≤ (SigmaVariableFull.numerator NineFeedbackStrength.originalH+newVariation NineFeedbackStrength.originalH)/(1-D0) :=
      div_le_div_of_nonneg_left hn' (sub_pos.mpr D0_lt_one)
        (by linarith only [D0FullDensity.finiteD_le_D0])
    _ ≤ _ := by
      rw [aProfile_eq]
      exact div_le_div_of_nonneg_right full_numerator_add_new_le (sub_pos.mpr D0_lt_one).le

/-- Preserve the whole paid coefficient variation and moving density, adding a disjoint loss. -/
def finiteProfile : ℝ :=
  (CorrectionD0Joint.numerator+Hf4Refine.finiteVariation NineFeedbackStrength.originalH+
    newVariation NineFeedbackStrength.originalH)/(1-D0FullDensity.finiteD)

theorem old_profile_lt : Hf4Refine.finiteProfile < finiteProfile := by
  apply div_lt_div_of_pos_right _ (sub_pos.mpr D0FullDensity.finiteD_lt_one)
  exact lt_add_of_pos_right _ newVariation_pos

theorem finiteProfile_pos : 0 < finiteProfile := Hf4Refine.finiteProfile_pos.trans old_profile_lt

/-- These two unconditional facts are the existing generic four-hc consumer's input. -/
theorem finiteProfile_le_actual :
    finiteProfile ≤ aProfile (nineProfile NineFeedbackStrength.originalH) := by
  apply le_trans (b := (SigmaVariableFull.numerator NineFeedbackStrength.originalH+
    newVariation NineFeedbackStrength.originalH)/(1-D0FullDensity.finiteD))
  · apply div_le_div_of_nonneg_right _ (sub_pos.mpr D0FullDensity.finiteD_lt_one).le
    exact add_le_add
      ((add_le_add CorrectionD0Joint.numerator_le le_rfl).trans
        (Hf4Refine.old_numerator_add_payment_le CoupledIntegralRecovery.originalH_nonneg)) le_rfl
  · exact full_profile_add_new_le_actual

def terminal : ℝ := log 2*finiteProfile+TerminalESigned.massPaid NineFeedbackStrength.originalH

theorem terminal_le_actual : terminal ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have ha := mul_le_mul_of_nonneg_left finiteProfile_le_actual (log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  have he := TerminalESigned.massPaid_le CoupledIntegralRecovery.originalH_nonneg
  have hm := TerminalECells.mass_le CoupledIntegralRecovery.originalH_nonneg
  unfold terminal
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [ha,he,hm]

theorem old_terminal_lt : Hf4Refine.terminal < terminal :=
  add_lt_add_left (mul_lt_mul_of_pos_left old_profile_lt (log_pos (by norm_num : (1:ℝ) < 2))) _

/-- The combined old/new numerator is paid once against the original unpaid ledger. -/
theorem joint_payment_le_original_unpaid :
    RemainingHf.splitLower 2*(Hf4Refine.finiteVariation NineFeedbackStrength.originalH+
      newVariation NineFeedbackStrength.originalH)/(1-D0FullDensity.finiteD) ≤ CorrectionD0Joint.allUnpaid := by
  have hl := mul_le_mul_of_nonneg_right
    (RemainingHf.splitLower_le (by norm_num : (1:ℝ) ≤ 2)) finiteProfile_pos.le
  have ht := terminal_le_actual
  rw [CorrectionD0Joint.actual_terminal_balance] at ht
  unfold terminal at ht
  have he : RemainingHf.splitLower 2*finiteProfile+TerminalESigned.massPaid NineFeedbackStrength.originalH =
      CorrectionD0Joint.terminal+RemainingHf.splitLower 2*
        (Hf4Refine.finiteVariation NineFeedbackStrength.originalH+newVariation NineFeedbackStrength.originalH)/
          (1-D0FullDensity.finiteD) := by
    unfold finiteProfile CorrectionD0Joint.terminal CorrectionD0Joint.profile
    ring
  linarith only [hl,ht,he]

end Hf4Continue
