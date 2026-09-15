import SigmaRationalOuterActual
import Hf4QuadModel

noncomputable section
namespace Hf4Quad
open Real TerminalE SigmaVariableOuterPayment SigmaVariableFull
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison F1FullRecoveryPayment

def low (x : ℝ) : ℝ := (x-1)*((1/30)+x*((-37/210)+x*((169/42)+x*((327/14)+x*((2213/42)+x*((11093/210)+x*((1649/70)+x*(155/42))))))))/(x^2*(x+1)^4*(x^2+8*x+1))

def up (x : ℝ) : ℝ :=
  (21*x*(x-1)*(x^2+10*x+1)*(x+1)^3+168*x^2*(x-1)*(x+1)^3+
    56*x^2*(x-1)^3*(x+1)-3*(x-1)^7)/(210*x^2*(x+1)^4)

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

def sl (x : ℝ) : ℝ := low ((x+1)/2)+low (2*x/(x+1))
def su (x : ℝ) : ℝ := up ((x+1)/2)+up (2*x/(x+1))

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
def kernel (t : ℝ) : ℝ :=
  (-(2145*t^2+4418*t+2280)/(210*(t+1)^2))*su ((t+2)/3)/t+
  (64*(10*t^4+18*t^3-t^2-6*t+3)/(945*t^4))*sl ((t+3)*(t+2)/(6*(t+1)))/t+
  (250*(-5*t^2+21*t+26)/(189*(-t^2+6*t+6)))*sl ((t^2+18*t+21)*(t+2)^2/(90*(t+1)^2))/t+
  (250*(-11*t^2+97*t+108)/(189*radical*(-t^2+6*t+6)))*
    sl ((t+9-2*radical)*(5+radical)/((t+9+2*radical)*(5-radical)))/t+
  SigmaRationalOuterFTC.jointNum t/SigmaRationalOuterFTC.jointDen t

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
