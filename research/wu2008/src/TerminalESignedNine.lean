import TerminalECollectedAffine
import Hf03OriginalTargets

noncomputable section
namespace TerminalESigned
open Real TerminalE NodeExtension FirstFeedbackIntegrals ActualNineFeedback
open scoped BigOperators

def logPaid (c x y : ℝ) : ℝ := RemainingHf.signed c (y/x)

theorem logPaid_le (c : ℝ) {x y : ℝ} (hx : 0<x) (hxy : x≤y) :
    logPaid c x y ≤ c*log y-c*log x := by
  have hy : 0<y := hx.trans_le hxy
  have h := RemainingHf.signed_le c ((one_le_div hx).mpr hxy)
  rw [log_div hy.ne' hx.ne'] at h
  unfold logPaid
  nlinarith only [h]

def cellPaid (a b : ℝ) : ℝ := rationalFull b-rationalFull a+
  logPaid coeffU a b+logPaid coeffThree (a+3) (b+3)+
  logPaid coeffOne (a+1) (b+1)+logPaid coeffSeven (a+7) (b+7)+
  logPaid coeffFive (3*a+5) (3*b+5)+
  logPaid (minusCoeff (3/4)) (leftMinus a) (leftMinus b)+
  logPaid (plusCoeff (3/4)) (leftPlus a) (leftPlus b)+
  logPaid (minusCoeff (2/3)-minusCoeff 2) (rightMinus a) (rightMinus b)+
  logPaid (plusCoeff (2/3)-plusCoeff 2) (rightPlus a) (rightPlus b)

theorem cellPaid_le {a b : ℝ} (ha : 1≤a) (hab : a≤b) : cellPaid a b≤cellMass a b := by
  have h0 := logPaid_le coeffU (by linarith : 0<a) hab
  have h3 := logPaid_le coeffThree (by linarith : 0<a+3) (by linarith : a+3≤b+3)
  have h1 := logPaid_le coeffOne (by linarith : 0<a+1) (by linarith : a+1≤b+1)
  have h7 := logPaid_le coeffSeven (by linarith : 0<a+7) (by linarith : a+7≤b+7)
  have h5 := logPaid_le coeffFive (by linarith : 0<3*a+5) (by linarith : 3*a+5≤3*b+5)
  have hp := affine_positive ha
  have hlm := logPaid_le (minusCoeff (3/4)) hp.1
    (by unfold leftMinus; linarith : leftMinus a≤leftMinus b)
  have hlp := logPaid_le (plusCoeff (3/4)) hp.2.1
    (by unfold leftPlus; linarith : leftPlus a≤leftPlus b)
  have hrm := logPaid_le (minusCoeff (2/3)-minusCoeff 2) hp.2.2.1
    (by
      unfold rightMinus
      have h : 0≤6-radical := by linarith only [radical_lt_four]
      nlinarith only [mul_nonneg h (sub_nonneg.mpr hab)] : rightMinus a≤rightMinus b)
  have hrp := logPaid_le (plusCoeff (2/3)-plusCoeff 2) hp.2.2.2
    (by
      unfold rightPlus
      have h : 0≤6+radical := by linarith only [radical_pos]
      nlinarith only [mul_nonneg h (sub_nonneg.mpr hab)] : rightPlus a≤rightPlus b)
  rw [cellMass_collected ha hab]
  unfold cellPaid affineLogs
  linarith only [h0,h3,h1,h7,h5,hlm,hlp,hrm,hrp]

def massPaid (z : Fin 9 → ℝ) : ℝ := ∑ k : Fin 9,z k*cellPaid (upperLeft k) (upperNode k)

theorem massPaid_le {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) : massPaid z≤TerminalECells.mass z := by
  apply Finset.sum_le_sum
  intro k _
  have hb := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have hc : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [hc] at hb
  exact mul_le_mul_of_nonneg_left (cellPaid_le hb.1 hb.2.1) (hz k)

/-- The original old sigma is retained, and old E is replaced, not added. -/
def finiteLower : ℝ := RemainingHf.splitLower 2*SigmaRemaining.finiteLower NineFeedbackStrength.originalH+
  massPaid NineFeedbackStrength.originalH

theorem finiteLower_le : finiteLower≤TerminalECells.lower := by
  have h := mul_le_mul_of_nonneg_right
    (RemainingHf.splitLower_le (by norm_num : (1:ℝ)≤2)) SigmaRemaining.original_finiteLower_pos.le
  have he := massPaid_le CoupledIntegralRecovery.originalH_nonneg
  unfold finiteLower TerminalECells.lower
  linarith only [h,he]

theorem finiteLower_le_actual : finiteLower≤firstFeedback NineFeedbackStrength.originalH 3 3 :=
  finiteLower_le.trans TerminalECells.lower_le
end TerminalESigned
