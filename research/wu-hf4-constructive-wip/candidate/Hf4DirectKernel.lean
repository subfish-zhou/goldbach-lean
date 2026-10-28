import Hf4DirectCoordinates

/-! UNCOMPILED direct371 kernel bridge. The coordinate lemmas in its imported
module passed root's strict algebra02 trial; this bridge has not yet run. -/
noncomputable section
namespace Hf4Quad

def directUpper (t : ℝ) : ℝ :=
  upZ ((t-1)/(t+11))+upZ ((t-1)/(3*(t+3)))

def directNegative (t : ℝ) : ℝ :=
  lowZ (t*(t-1)/(t^2+23*t+24))+lowZ (t*(t-1)/(3*(t^2+7*t+8)))

def directQuadratic (t : ℝ) : ℝ :=
  let n := (t^2+18*t+21)*(t+2)^2
  let d := 90*(t+1)^2
  lowZ ((n-d)/(n+3*d))+lowZ ((n-d)/(3*n+d))

def directRadical (t : ℝ) : ℝ :=
  let n := TerminalE.radical*(t-1)
  let a := 10*(t+3)
  lowZ (n/(a-n))+lowZ (n/(a+n))

def directKernel (t : ℝ) : ℝ :=
  (-(2145*t^2+4418*t+2280)/(210*(t+1)^2))*directUpper t/t+
  (64*(10*t^4+18*t^3-t^2-6*t+3)/(945*t^4))*directNegative t/t+
  (250*(-5*t^2+21*t+26)/(189*(-t^2+6*t+6)))*directQuadratic t/t+
  (250*(-11*t^2+97*t+108)/(189*TerminalE.radical*(-t^2+6*t+6)))*directRadical t/t+
  SigmaRationalOuterFTC.jointNum t/SigmaRationalOuterFTC.jointDen t

theorem compactKernel_eq_directKernel {t : ℝ} (ht : 1 ≤ t) :
    compactKernel t = directKernel t := by
  have h0 := DirectCoordinates.zero_coordinates t
  have h1 := DirectCoordinates.negative_coordinates ht
  have hq := DirectCoordinates.quotient_coordinates
    (n := (t^2+18*t+21)*(t+2)^2) (DirectCoordinates.quadratic_den_ne ht)
  have hr := DirectCoordinates.conjugate_coordinates
    (a := 5*(t+3)) (b := TerminalE.radical*(t-1)) (DirectCoordinates.radical_den_ne ht)
  have ha : 2*(5*(t+3)) = (10:ℝ)*(t+3) := by ring
  simp only [ha] at hr
  simp only [compactKernel, directKernel, directUpper, directNegative,
    directQuadratic, directRadical, slCompact, suCompact,
    h0.1, h0.2, h1.1, h1.2, hq.1, hq.2,
    DirectCoordinates.radical_argument t, hr.1, hr.2]

end Hf4Quad
#print axioms Hf4Quad.compactKernel_eq_directKernel
