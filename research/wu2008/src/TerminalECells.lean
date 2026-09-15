import TerminalEFullFTC
import SigmaPrimitiveCells
namespace TerminalECells
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals ActualNineFeedback
open scoped Interval BigOperators
noncomputable section

def mass (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9,z k*TerminalE.cellMass (upperLeft k) (upperNode k)

theorem mass_le {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    aProfile (nineProfile z)*log 2+mass z ≤ eProfile (nineProfile z) 3 := by
  have hw : ContinuousOn (fun t : ℝ => log ((t+1)/2)/t) (uIcc 1 3) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (1:ℝ)≤3)] at ht
    have ht0 : 0<t := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have he := profile_integral_cells z le_rfl (by norm_num [upperNode]) hw
  have hm : mass z ≤ ∫ t in (1:ℝ)..3,nineProfile z t*(log ((t+1)/2)/t) := by
    rw [he]
    apply Finset.sum_le_sum
    intro k _
    have hb := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
    have hc : cellLeft 1 k=upperLeft k := by
      unfold cellLeft upperLeft
      split_ifs <;> rfl
    rw [hc] at hb ⊢
    exact mul_le_mul_of_nonneg_left (TerminalE.cellMass_le hb.1 hb.2.1) (hz k)
  unfold eProfile
  norm_num only [show (3:ℝ)-1=2 by norm_num,show (3:ℝ)-2=1 by norm_num,
    show (4:ℝ)/2=2 by norm_num]
  apply add_le_add le_rfl
  simpa only [div_mul_eq_mul_div,mul_div_assoc] using hm

/-- Old sigma retained, with the entire newly integrated E density. -/
def lower : ℝ := log 2*SigmaRemaining.finiteLower NineFeedbackStrength.originalH+
  mass NineFeedbackStrength.originalH

theorem lower_le : lower ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have he := mass_le CoupledIntegralRecovery.originalH_nonneg
  have ha := mul_le_mul_of_nonneg_left SigmaRemaining.original_finiteLower
    (log_nonneg (by norm_num : (1:ℝ)≤2))
  unfold lower
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  linarith only [he,ha]

/-- Both completed integral branches can now meet in the same original terminal. -/
def jointLower : ℝ := log 2*SigmaPrimitiveCells.profileLower+
  max (RemainingHf.paidCells NineFeedbackStrength.originalH 3) (mass NineFeedbackStrength.originalH)

theorem jointLower_le : jointLower ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  have he := mass_le CoupledIntegralRecovery.originalH_nonneg
  have ho := RemainingHf.paidCells_le CoupledIntegralRecovery.originalH_nonneg
    (by norm_num : (3:ℝ)≤3) (by norm_num [upperNode] : (3:ℝ)-2≤upperNode 0)
  norm_num only [show (3:ℝ)-1=2 by norm_num,show (4:ℝ)/2=2 by norm_num] at ho
  have ha := mul_le_mul_of_nonneg_left SigmaPrimitiveCells.profileLower_le
    (log_nonneg (by norm_num : (1:ℝ)≤2))
  unfold jointLower
  simp only [firstFeedback,profileJ,intervalIntegral.integral_same,zero_div,add_zero]
  rcases le_total (RemainingHf.paidCells NineFeedbackStrength.originalH 3)
    (mass NineFeedbackStrength.originalH) with h|h
  · rw [max_eq_right h]
    linarith only [he,ha]
  · rw [max_eq_left h]
    linarith only [ho,ha]
end
end TerminalECells
