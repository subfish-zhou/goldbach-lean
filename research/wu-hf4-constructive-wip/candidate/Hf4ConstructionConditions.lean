import Hf4ConstructionRounding
import Hf4QuadRatCore

/-! UNCOMPILED original-formula constructors. Hf4QuadRatCore is the existing
scratch pure-rational layer. No change to error budget or coefficient precision. -/
namespace Hf4Quad.Construction
open RationalModel

def withError (p : Certificate) (e : ℚ) : Certificate := ⟨p.a,p.b,p.c,p.d,e⟩

def addCoefficients (p q : Certificate) : Certificate :=
  ⟨floorD (p.a+q.a),floorD (p.b+q.b),floorD (p.c+q.c),floorD (p.d+q.d),0⟩

def addRequired (p q r : Certificate) : ℚ :=
  p.error+q.error+|p.a+q.a-r.a|+|p.b+q.b-r.b|+
    |p.c+q.c-r.c|+|p.d+q.d-r.d|

def constructAdd (p q : Certificate) : Certificate :=
  let r := addCoefficients p q
  withError r (upD (addRequired p q r))

/-- The lower four convolution coefficients; the other three are NOT discarded
from error control: mulRequired uses the complete original degree-six residual. -/
def mulCoefficients (p q : Certificate) : Certificate :=
  ⟨floorD (p.a*q.a),floorD (p.a*q.b+p.b*q.a),
    floorD (p.a*q.c+p.b*q.b+p.c*q.a),
    floorD (p.a*q.d+p.b*q.c+p.c*q.b+p.d*q.a),0⟩

def mulRequired (p q r : Certificate) : ℚ :=
  p.error*q.norm+q.error*p.norm+p.error*q.error+residual p q r

def constructMul (p q : Certificate) : Certificate :=
  let r := mulCoefficients p q
  withError r (upD (mulRequired p q r))

/-- All inverse-series coefficients are unrounded until the final record.
Lean Rat division is total. Python compatibility on valid input follows from
error>=0 and lower>0; no nonzero premise is needed by inv_condition below. -/
def invCoefficients (p : Certificate) : Certificate :=
  let z0 := 1/p.a
  let z1 := -(p.b*z0)/p.a
  let z2 := -(p.b*z1+p.c*z0)/p.a
  let z3 := -(p.b*z2+p.c*z1+p.d*z0)/p.a
  ⟨floorD z0,floorD z1,floorD z2,floorD z3,0⟩

def invRequired (p q : Certificate) : ℚ :=
  residual p q ⟨1,0,0,0,0⟩+q.norm*p.error

def constructInv (p : Certificate) : Certificate :=
  let q := invCoefficients p
  withError q (upD (invRequired p q / lower p))

/-- No new sign hypothesis on p.error or q.error. -/
theorem add_condition (p q : Certificate) : addCondition p q (constructAdd p q) := by
  change addRequired p q (addCoefficients p q) ≤ upD (addRequired p q (addCoefficients p q))
  exact le_upD _

/-- The unchanged residual absorbs all coefficient rounding and degree-six tail. -/
theorem mul_condition (p q : Certificate) : mulCondition p q (constructMul p q) := by
  change mulRequired p q (mulCoefficients p q) ≤ upD (mulRequired p q (mulCoefficients p q))
  exact le_upD _

/-- The old positive lower enclosure is the only required numerical guard. -/
theorem inv_condition (p : Certificate) (hL : 0 < lower p) :
    invCondition p (constructInv p) := by
  constructor
  · exact hL
  · change invRequired p (invCoefficients p) ≤
      lower p * upD (invRequired p (invCoefficients p) / lower p)
    simpa only [mul_comm] using
      (div_le_iff₀ hL).mp (le_upD (invRequired p (invCoefficients p) / lower p))

end Hf4Quad.Construction
