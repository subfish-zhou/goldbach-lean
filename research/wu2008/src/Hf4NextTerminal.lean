import Hf4NextCells

noncomputable section
namespace Hf4Next
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals ActualNineFeedback
open scoped BigOperators

/-- The original nine-cell H-weighted sum; no new subdivision or reference profile. -/
def finiteVariation (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9, z k * cellPayment (upperLeft k) (upperNode k)

theorem old_finiteVariation_le {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    SigmaEndpointPayment.finiteVariation z ≤ finiteVariation z := by
  apply Finset.sum_le_sum
  intro k _
  obtain ⟨ha,hab,_⟩ := SigmaEndpointPayment.original_cell_bounds k
  exact mul_le_mul_of_nonneg_left (old_cellPayment_le ha hab) (hz k)

theorem finiteVariation_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    0 ≤ finiteVariation z :=
  (SigmaEndpointPayment.finiteVariation_nonneg hz).trans (old_finiteVariation_le hz)

theorem original_cell_strict (k : Fin 9) : upperLeft k < upperNode k := by
  have hk : (0:ℝ) ≤ k.val := Nat.cast_nonneg _
  unfold upperLeft upperNode
  split_ifs <;> linarith

theorem old_finiteVariation_lt {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    (hpos : ∃ k, 0 < z k) :
    SigmaEndpointPayment.finiteVariation z < finiteVariation z := by
  apply Finset.sum_lt_sum
  · intro k _
    obtain ⟨ha,hab,_⟩ := SigmaEndpointPayment.original_cell_bounds k
    exact mul_le_mul_of_nonneg_left (old_cellPayment_le ha hab) (hz k)
  · obtain ⟨k,hk⟩ := hpos
    refine ⟨k, Finset.mem_univ k, ?_⟩
    exact mul_lt_mul_of_pos_left
      (old_cellPayment_lt (SigmaEndpointPayment.original_cell_bounds k).1 (original_cell_strict k)) hk

/-- Positivity is inherited from the already-paid original numerator, not evaluated anew. -/
theorem original_has_positive_weight : ∃ k, 0 < NineFeedbackStrength.originalH k := by
  by_contra hn
  push Not at hn
  have hz (k : Fin 9) : NineFeedbackStrength.originalH k = 0 :=
    le_antisymm (hn k) (CoupledIntegralRecovery.originalH_nonneg k)
  have hp := SigmaInnerProfile.original_numerator_pos
  simp only [SigmaInnerProfile.numerator, hz, zero_mul, Finset.sum_const_zero] at hp
  exact (lt_irrefl 0) hp

theorem original_variation_strict :
    SigmaEndpointPayment.finiteVariation NineFeedbackStrength.originalH <
      finiteVariation NineFeedbackStrength.originalH :=
  old_finiteVariation_lt CoupledIntegralRecovery.originalH_nonneg original_has_positive_weight

/-- Consume the genuinely new cell estimates on the same original numerator. -/
theorem old_numerator_add_payment_le {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    SigmaInnerProfile.numerator z + finiteVariation z ≤ SigmaVariableFull.numerator z := by
  unfold SigmaInnerProfile.numerator finiteVariation SigmaVariableFull.numerator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  obtain ⟨ha,hab,hb⟩ := SigmaEndpointPayment.original_cell_bounds k
  simpa only [mul_add] using mul_le_mul_of_nonneg_left (old_cell_add_payment_le ha hab hb) (hz k)

/-- Preserve the pre-existing common maximum inside CorrectionD0Joint.numerator. -/
def finiteProfile : ℝ :=
  (CorrectionD0Joint.numerator + finiteVariation NineFeedbackStrength.originalH)/
    (1-D0FullDensity.finiteD)

theorem old_profile_lt : SigmaEndpointPayment.finiteProfile < finiteProfile := by
  apply div_lt_div_of_pos_right _ (sub_pos.mpr D0FullDensity.finiteD_lt_one)
  exact add_lt_add_right original_variation_strict _

theorem finiteProfile_pos : 0 < finiteProfile :=
  SigmaEndpointPayment.finiteProfile_pos.trans old_profile_lt

theorem finiteProfile_le_full :
    finiteProfile ≤ SigmaVariableFull.profile NineFeedbackStrength.originalH := by
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr D0FullDensity.finiteD_lt_one).le
  exact (add_le_add CorrectionD0Joint.numerator_le le_rfl).trans
    (old_numerator_add_payment_le CoupledIntegralRecovery.originalH_nonneg)

/-- The original log multiplier and signed E, with E present exactly once. -/
def terminal : ℝ := log 2*finiteProfile + TerminalESigned.massPaid NineFeedbackStrength.originalH

/-- Unconditional lower payment on the literal original hf4 right hand side. -/
theorem terminal_le_actual :
    terminal ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  apply le_trans (b := SigmaVariableFull.terminal)
  · exact add_le_add
      (mul_le_mul_of_nonneg_left finiteProfile_le_full (log_nonneg (by norm_num : (1:ℝ) ≤ 2))) le_rfl
  · exact SigmaVariableFull.terminal_le_actual

/-- Strict improvement over the old finite-variation terminal, not a max wrapper. -/
theorem old_finiteTerminal_lt : SigmaEndpointPayment.finiteTerminal < terminal := by
  have hl := mul_le_mul_of_nonneg_right
    (RemainingHf.splitLower_le (by norm_num : (1:ℝ) ≤ 2)) SigmaEndpointPayment.finiteProfile_pos.le
  have hp := mul_lt_mul_of_pos_left old_profile_lt (log_pos (by norm_num : (1:ℝ) < 2))
  unfold SigmaEndpointPayment.finiteTerminal terminal
  exact add_lt_add_left (hl.trans_lt hp) _

/-- Keep a wholly algebraic payment in the original unpaid ledger as well. -/
theorem rational_payment_le_original_unpaid :
    RemainingHf.splitLower 2 * finiteVariation NineFeedbackStrength.originalH /
      (1-D0FullDensity.finiteD) ≤ CorrectionD0Joint.allUnpaid := by
  have hl := mul_le_mul_of_nonneg_right
    (RemainingHf.splitLower_le (by norm_num : (1:ℝ) ≤ 2)) finiteProfile_pos.le
  have ht := terminal_le_actual
  rw [CorrectionD0Joint.actual_terminal_balance] at ht
  unfold terminal at ht
  have hbal : RemainingHf.splitLower 2*finiteProfile+
      TerminalESigned.massPaid NineFeedbackStrength.originalH =
      CorrectionD0Joint.terminal + RemainingHf.splitLower 2 *
        finiteVariation NineFeedbackStrength.originalH/(1-D0FullDensity.finiteD) := by
    unfold finiteProfile CorrectionD0Joint.terminal CorrectionD0Joint.profile
    ring
  linarith only [hl,ht,hbal]

end Hf4Next
