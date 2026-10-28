import WR2ClassicalSixthAssembly
import WR2ExactRationalLog

/-! Exact midpoint-table checks with the original grid and rational payments. -/

namespace WuPaper.ClassicalSixthTableCheck
open ExactRational

def R : ℚ := 1327/200
def r : ℚ := 1327/824
def u (s : ℚ) : ℚ := R-1-s
def v (s : ℚ) : ℚ := R-r-s
def split : ℚ := (1/2-2*(25/206))/(100/1327)
def endpoint : ℚ := (1/2-(100/1327)-(25/206))/(100/1327)

def value (ratio s : ℚ) : ℚ := logLo ratio*logLo (s-1)/(s*(1-2*(100/1327)*s))
def lowerValue (s : ℚ) : ℚ := value (r*u s/v s) s
def upperValue (s : ℚ) : ℚ := value (u s*v s/r) s

@[simp] theorem cast_value (ratio s : ℚ) :
    (value ratio s : ℝ) = ClassicalSixthRational.value (ratio : ℝ) (s : ℝ) := by
  simp [value, ClassicalSixthRational.value, QuarterTrim.alpha]

@[simp] theorem cast_lowerValue (s : ℚ) :
    (lowerValue s : ℝ) = ClassicalSixthRational.lowerValue (s : ℝ) := by
  simp [lowerValue, ClassicalSixthRational.lowerValue, u, v, R, r,
    ClassicalSixthBranch.u, ClassicalSixthBranch.v, ClassicalSixthBranch.R,
    ClassicalSixthBranch.r]

@[simp] theorem cast_upperValue (s : ℚ) :
    (upperValue s : ℝ) = ClassicalSixthRational.upperValue (s : ℝ) := by
  simp [upperValue, ClassicalSixthRational.upperValue, u, v, R, r,
    ClassicalSixthBranch.u, ClassicalSixthBranch.v, ClassicalSixthBranch.R,
    ClassicalSixthBranch.r]

def lowerCondition (q : ℕ → ℕ) (i : ℕ) : Prop :=
  (q i : ℚ)/1000000000000 ≤ lowerValue (midpoint 2 split 4096 i)
def upperCondition (q : ℕ → ℕ) (i : ℕ) : Prop :=
  (q i : ℚ)/1000000000000 ≤ upperValue (midpoint split endpoint 4096 i)

theorem lowerCondition_sound {q : ℕ → ℕ} {i : ℕ} (h : lowerCondition q i) :
    (q i : ℝ)/1000000000000 ≤ ClassicalSixthRational.lowerValue
      ((ClassicalSixthQuadrature.point 2 WuSource.SrcSixthGain.split 4096 i +
        ClassicalSixthQuadrature.point 2 WuSource.SrcSixthGain.split 4096 (i+1))/2) := by
  have hh := Rat.cast_le (K := ℝ) |>.mpr h
  simpa [ExactRational.midpoint, split, WuSource.SrcSixthGain.split, QuarterTrim.alpha,
    QuarterTrim.beta, ClassicalSixthQuadrature.point, ClassicalSixthQuadrature.step] using hh

theorem upperCondition_sound {q : ℕ → ℕ} {i : ℕ} (h : upperCondition q i) :
    (q i : ℝ)/1000000000000 ≤ ClassicalSixthRational.upperValue
      ((ClassicalSixthQuadrature.point WuSource.SrcSixthGain.split WuSource.SrcSixthGain.endpoint 4096 i +
        ClassicalSixthQuadrature.point WuSource.SrcSixthGain.split WuSource.SrcSixthGain.endpoint 4096 (i+1))/2) := by
  have hh := Rat.cast_le (K := ℝ) |>.mpr h
  simpa [ExactRational.midpoint, split, endpoint, WuSource.SrcSixthGain.split, WuSource.SrcSixthGain.endpoint,
    QuarterTrim.alpha, QuarterTrim.beta, ClassicalSixthQuadrature.point,
    ClassicalSixthQuadrature.step] using hh

end WuPaper.ClassicalSixthTableCheck
