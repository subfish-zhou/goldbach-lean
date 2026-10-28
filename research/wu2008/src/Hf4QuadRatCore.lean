import Mathlib.Algebra.Order.Field.Rat

namespace Hf4Quad.RationalModel
structure Certificate where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  error : ℚ
  deriving DecidableEq


def Certificate.norm (p : Certificate) : ℚ := |p.a|+|p.b|+|p.c|+|p.d|


def addCondition (p q r : Certificate) : Prop :=
  p.error+q.error+|p.a+q.a-r.a|+|p.b+q.b-r.b|+
    |p.c+q.c-r.c|+|p.d+q.d-r.d| ≤ r.error

def residual (p q r : Certificate) : ℚ :=
  |p.a*q.a-r.a|+|p.a*q.b+p.b*q.a-r.b|+
  |p.a*q.c+p.b*q.b+p.c*q.a-r.c|+
  |p.a*q.d+p.b*q.c+p.c*q.b+p.d*q.a-r.d|+
  |p.b*q.d+p.c*q.c+p.d*q.b|+|p.c*q.d+p.d*q.c|+|p.d*q.d|

def mulCondition (p q r : Certificate) : Prop :=
  p.error*q.norm+q.error*p.norm+p.error*q.error+residual p q r ≤ r.error

def lower (p : Certificate) : ℚ := |p.a|-|p.b|-|p.c|-|p.d|-p.error

def invCondition (p q : Certificate) : Prop :=
  0 < lower p ∧ residual p q ⟨1,0,0,0,0⟩+q.norm*p.error ≤ lower p*q.error

instance (p q r : Certificate) : Decidable (addCondition p q r) :=
  inferInstanceAs (Decidable (_ ≤ _))
instance (p q r : Certificate) : Decidable (mulCondition p q r) :=
  inferInstanceAs (Decidable (_ ≤ _))
instance (p q : Certificate) : Decidable (invCondition p q) :=
  inferInstanceAs (Decidable (_ ∧ _))


def neg (p : Certificate) : Certificate := ⟨-p.a,-p.b,-p.c,-p.d,p.error⟩


/-- Exact addition of certificates introduces no rounding error. -/
def addExact (p q : Certificate) : Certificate :=
  ⟨p.a+q.a,p.b+q.b,p.c+q.c,p.d+q.d,p.error+q.error⟩


/-- Exact scalar multiplication keeps the original error certificate. -/
def scale (s : ℚ) (p : Certificate) : Certificate :=
  ⟨s*p.a,s*p.b,s*p.c,s*p.d,|s| * p.error⟩

end Hf4Quad.RationalModel
