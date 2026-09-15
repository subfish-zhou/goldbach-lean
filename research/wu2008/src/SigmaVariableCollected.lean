import SigmaVariableOuterProfile

noncomputable section
namespace SigmaVariableFull
open Real TerminalE FirstCRationalPayment

/-- Coefficients are collected before making any signed logarithmic payment. -/
def logZeroCoeff (p : ℝ) : ℝ := k+c+d+TerminalE.e+f+h-zeroOne p
def logNegCoeff (p : ℝ) : ℝ := -c-d-TerminalE.e-f-negOne p
def logQuadCoeff (p : ℝ) : ℝ := (-h-quadOne p)/2
def logRadCoeff (p : ℝ) : ℝ :=
  ((g-8*h-quadZero p)-4*(-h-quadOne p))/(2*radical)

/-- All repeated principal parts survive unchanged. -/
def jointRational (p x : ℝ) : ℝ :=
  (-a+zeroTwo p)/x-b/(2*x^2)+
  (d+TerminalE.e+f+negTwo p)/(x+1)+
  (TerminalE.e+f+negThree p)/(2*(x+1)^2)+(f+negFour p)/(3*(x+1)^3)

def jointPrimitive (p x : ℝ) : ℝ :=
  logZeroCoeff p*log x+logNegCoeff p*log (x+1)-mainCoeff p*log (x-p)+
  logQuadCoeff p*log (q x)+
  logRadCoeff p*(log (x+4-radical)-log (x+4+radical))+jointRational p x

theorem jointPrimitive_identity (p x : ℝ) :
    jointPrimitive p x=D0FullDensity.zeroPrimitive x-TerminalE.primitive p x := by
  unfold jointPrimitive logZeroCoeff logNegCoeff logQuadCoeff logRadCoeff jointRational
    D0FullDensity.zeroPrimitive TerminalE.primitive quadraticPrimitive polePrimitive
  simp only [sub_zero,sub_neg_eq_add,zero_div,sub_zero]
  ring

/-- The exact outer integrand is a difference of these same collected primitives. -/
theorem endpointMass_collected (t : ℝ) :
    endpointMass t=jointPrimitive (-(t+1)) ((t+1)/2)-jointPrimitive (-(t+1)) 1 := by
  rw [jointPrimitive_identity,jointPrimitive_identity]
  unfold endpointMass
  ring

/-- Logs at identical arguments are combined; no sign has been inferred numerically. -/
def collectedMass (t : ℝ) : ℝ :=
  logZeroCoeff (-(t+1))*log ((t+1)/2)+
  logNegCoeff (-(t+1))*(log ((t+1)/2+1)-log 2)-
  mainCoeff (-(t+1))*(log ((t+1)/2-(-(t+1)))-log (1-(-(t+1))))+
  logQuadCoeff (-(t+1))*(log (q ((t+1)/2))-log (q 1))+
  logRadCoeff (-(t+1))*(log ((t+1)/2+4-radical)-log ((t+1)/2+4+radical)-
    log (1+4-radical)+log (1+4+radical))+
  jointRational (-(t+1)) ((t+1)/2)-jointRational (-(t+1)) 1

theorem collectedMass_identity (t : ℝ) : collectedMass t=endpointMass t := by
  rw [endpointMass_collected]
  unfold collectedMass jointPrimitive
  simp only [log_one,mul_zero]
  norm_num
  ring

theorem collected_density_integral {t : ℝ} (ht : t ∈ Set.Icc 1 3) :
    (∫ v in (3:ℝ)..t+2,density t v)=collectedMass t := by
  rw [density_integral ht,collectedMass_identity,endpointMass_eq ht]

end SigmaVariableFull
