import Mathlib.Data.Real.Basic

noncomputable section
namespace SigmaRationalOuterFTC
/-- Both original rational endpoints, after cancellation and division by the outer t. -/
def jointNum (t : ℝ) : ℝ :=
  32/35-(184/105)*t-(1144/945)*t^2-(5261/540)*t^3+(176/63)*t^4+
  (1759/270)*t^5+(2122/945)*t^6+(299/1260)*t^7

def jointDen (t : ℝ) : ℝ := t^4*(t+1)*(t+3)^3

end SigmaRationalOuterFTC
