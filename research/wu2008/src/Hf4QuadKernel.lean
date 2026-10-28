import Hf4QuadKernelData
import SigmaRationalOuterActual
import Hf4QuadModel

noncomputable section
namespace Hf4Quad
open Real TerminalE SigmaVariableOuterPayment SigmaVariableFull
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison F1FullRecoveryPayment

theorem low_eq {x : ℝ} (hx : 1 ≤ x) : low x = RemainingHf.basicLower x := by
  rw [TerminalE.basic_partial hx]
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x+1 ≠ 0 := by linarith
  have hq : x^2+8*x+1 ≠ 0 := by positivity
  unfold low basicPartial TerminalE.h TerminalE.k TerminalE.a TerminalE.b TerminalE.c
    TerminalE.d TerminalE.e TerminalE.f TerminalE.g TerminalE.q
  field_simp [hx0,hx1,hq]
  ring

theorem up_eq {x : ℝ} (hx : 1 ≤ x) : up x = RemainingHf.basicUpper x := by
  have hh := SigmaRationalOuterFTC.upper_homogeneous
    (by linarith : 0 < x) (by norm_num : (0:ℝ)<1)
  simpa [up,SigmaRationalOuterFTC.upperNum,SigmaRationalOuterFTC.upperDen] using hh.symm

theorem sl_eq {x : ℝ} (hx : 1 ≤ x) : sl x = RemainingHf.splitLower x := by
  unfold sl RemainingHf.splitLower Wu04FactorEnvelopes.leftFactor Wu04FactorEnvelopes.rightFactor
  rw [low_eq (by linarith : 1 ≤ (x+1)/2),low_eq]
  · simp only [add_comm x 1]
  · apply (le_div_iff₀ (by linarith : 0 < x+1)).mpr
    linarith

theorem su_eq {x : ℝ} (hx : 1 ≤ x) : su x = RemainingHf.splitUpper x := by
  unfold su RemainingHf.splitUpper Wu04FactorEnvelopes.leftFactor Wu04FactorEnvelopes.rightFactor
  rw [up_eq (by linarith : 1 ≤ (x+1)/2),up_eq]
  · simp only [add_comm x 1]
  · apply (le_div_iff₀ (by linarith : 0 < x+1)).mpr
    linarith

/-- Signed terms remain jointly added; rational endpoint cancellation is already exact. -/
theorem kernel_eq {t : ℝ} (ht : t ∈ Set.Icc 1 3) : kernel t = paidWeight t := by
  have h0 := su_eq (zeroRatio_ge ht.1)
  have h1 := sl_eq (negRatio_ge ht.1)
  have hq := sl_eq (quadRatio_ge ht.1)
  have hr := sl_eq (radRatio_ge ht.1)
  unfold zeroRatio at h0
  unfold negRatio at h1
  unfold quadRatio at hq
  unfold radRatio at hr
  unfold kernel paidWeight paidMass
  rw [h0,h1,hq,hr,zero_coefficient_formula ht.1,neg_coefficient_formula ht.1,
    quad_coefficient_formula ht,rad_coefficient_formula ht]
  have hj := SigmaRationalOuterFTC.joint_weight_identity ht.1
  unfold zeroRatio negRatio quadRatio radRatio
  linear_combination -hj

end Hf4Quad
