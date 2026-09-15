import Hf4ContinueTerminal

noncomputable section
namespace Hf4Den
open Real NodeExtension FirstFeedbackIntegrals ActualNineFeedback
open scoped BigOperators

/-- Strictness of the existing envelope, using the frozen certificate only. -/
theorem splitLower_lt {x : ℝ} (hx : 1 < x) : RemainingHf.splitLower x < log x := by
  have hl : 1 < Wu04FactorEnvelopes.leftFactor x := by
    unfold Wu04FactorEnvelopes.leftFactor
    linarith
  have hp := Hf4Continue.denominatorPayment_pos hl
  have hd := Hf4Continue.denominatorPayment_le hl.le
  have hr := RemainingHf.basicLower_le (Wu04FactorEnvelopes.factors hx.le).2.1
  rw [Wu04FactorEnvelopes.exact_log hx.le]
  unfold RemainingHf.splitLower
  linarith only [hp,hd,hr]

/-- A positive signed atom has strict endpoint slack on a nondegenerate cell. -/
theorem logPaid_lt {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hxy : x < y) :
    TerminalESigned.logPaid c x y < c*log y-c*log x := by
  have h := mul_lt_mul_of_pos_left (splitLower_lt ((one_lt_div hx).mpr hxy)) hc
  rw [log_div (hx.trans hxy).ne' hx.ne'] at h
  simpa only [TerminalESigned.logPaid,RemainingHf.signed,if_pos hc.le,mul_sub] using h

/-- The old signed E atoms remain once-collected; only strictness is new. -/
theorem cellPaid_lt {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    TerminalESigned.cellPaid a b < TerminalE.cellMass a b := by
  have hp := TerminalESigned.affine_positive ha
  have h0 := TerminalESigned.logPaid_le TerminalESigned.coeffU (by linarith : 0<a) hab.le
  have h3 := TerminalESigned.logPaid_le TerminalESigned.coeffThree
    (by linarith : 0<a+3) (by linarith : a+3≤b+3)
  have h1 := TerminalESigned.logPaid_le TerminalESigned.coeffOne
    (by linarith : 0<a+1) (by linarith : a+1≤b+1)
  have h7 := logPaid_lt TerminalESigned.coefficient_signs.2.2.2.1
    (by linarith : 0<a+7) (by linarith : a+7<b+7)
  have h5 := TerminalESigned.logPaid_le TerminalESigned.coeffFive
    (by linarith : 0<3*a+5) (by linarith : 3*a+5≤3*b+5)
  have hlm := TerminalESigned.logPaid_le (TerminalESigned.minusCoeff (3/4)) hp.1
    (by unfold TerminalESigned.leftMinus; linarith :
      TerminalESigned.leftMinus a≤TerminalESigned.leftMinus b)
  have hlp := TerminalESigned.logPaid_le (TerminalESigned.plusCoeff (3/4)) hp.2.1
    (by unfold TerminalESigned.leftPlus; linarith :
      TerminalESigned.leftPlus a≤TerminalESigned.leftPlus b)
  have hrm := TerminalESigned.logPaid_le
    (TerminalESigned.minusCoeff (2/3)-TerminalESigned.minusCoeff 2) hp.2.2.1
    (by
      unfold TerminalESigned.rightMinus
      have h : 0≤6-TerminalE.radical := by linarith only [TerminalE.radical_lt_four]
      nlinarith only [mul_nonneg h (sub_nonneg.mpr hab.le)] :
      TerminalESigned.rightMinus a≤TerminalESigned.rightMinus b)
  have hrp := TerminalESigned.logPaid_le
    (TerminalESigned.plusCoeff (2/3)-TerminalESigned.plusCoeff 2) hp.2.2.2
    (by
      unfold TerminalESigned.rightPlus
      have h : 0≤6+TerminalE.radical := by linarith only [TerminalE.radical_pos]
      nlinarith only [mul_nonneg h (sub_nonneg.mpr hab.le)] :
      TerminalESigned.rightPlus a≤TerminalESigned.rightPlus b)
  rw [TerminalESigned.cellMass_collected ha hab.le]
  unfold TerminalESigned.cellPaid TerminalESigned.affineLogs
  linarith only [h0,h3,h1,h7,h5,hlm,hlp,hrm,hrp]

/-- The certified full E endpoint expression is strictly stronger at the original H. -/
theorem original_E_strict :
    TerminalESigned.massPaid NineFeedbackStrength.originalH <
      TerminalECells.mass NineFeedbackStrength.originalH := by
  apply Finset.sum_lt_sum
  · intro k _
    obtain ⟨ha,hab,_⟩ := SigmaEndpointPayment.original_cell_bounds k
    exact mul_le_mul_of_nonneg_left (TerminalESigned.cellPaid_le ha hab)
      (CoupledIntegralRecovery.originalH_nonneg k)
  · obtain ⟨k,hk⟩ := Hf4Next.original_has_positive_weight
    exact ⟨k,Finset.mem_univ k,mul_lt_mul_of_pos_left
      (cellPaid_lt (SigmaEndpointPayment.original_cell_bounds k).1
        (Hf4Next.original_cell_strict k)) hk⟩

theorem original_eUnpaid_pos : 0 < TerminalESigned.eUnpaid :=
  sub_pos.mpr original_E_strict

end Hf4Den
