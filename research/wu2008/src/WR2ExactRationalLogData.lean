import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Pure rational definitions of the existing twelve-term log bounds and midpoint. -/
namespace WuPaper.ExactRational
open Finset

def logLo (t : ℚ) : ℚ :=
  2 * ∑ i ∈ range 12, ((t-1)/(t+1))^(2*i+1)/(2*i+1 : ℚ)

def logHi (t : ℚ) : ℚ :=
  logLo t + 2*((t-1)/(t+1))^25/(1-((t-1)/(t+1))^2)

/-- The same midpoint formula used by both existing quadrature assemblies. -/
def midpoint (a b : ℚ) (n i : ℕ) : ℚ :=
  (a+(b-a)/n*i + (a+(b-a)/n*(i+1)))/2

end WuPaper.ExactRational
