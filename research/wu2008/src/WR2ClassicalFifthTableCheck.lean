import WR2ClassicalFifthPolynomialData
import WR2ClassicalFifthAssembly
import WR2ExactRationalLog

/-! Exact evaluation of the unchanged fifth-slot polynomial and midpoint tables. -/

namespace WuPaper.ClassicalFifthTableCheck
open ExactRational

def lo : ℚ := (1/2-2*(25/206))/(100/1327)
def cut : ℚ := (1/2-(100/1327)-(25/206))/(100/1327)
def hi : ℚ := 1327/200-2

def value (extra ratio s : ℚ) : ℚ :=
  (logLo (s-1)+extra)*logLo ratio/(s*(1/2-(100/1327)*s))
def initialValue (s : ℚ) : ℚ := value 0 ((1327/824)/(1327/200-1327/824-s)) s
def middleValue (s : ℚ) : ℚ := value (cPoly (s-4)) ((1327/824)/(1327/200-1327/824-s)) s
def terminalValue (s : ℚ) : ℚ := value (cPoly (s-4)) (1327/200-1-s) s

@[simp] theorem cast_cPoly (s : ℚ) :
    (cPoly s : ℝ) = ClassicalCPolynomial.cPoly (s : ℝ) := by
  simp [cPoly, ClassicalCPolynomial.cPoly]

@[simp] theorem cast_value (extra ratio s : ℚ) :
    (value extra ratio s : ℝ) = ClassicalFifthRational.value (extra : ℝ) (ratio : ℝ) (s : ℝ) := by
  simp [value, ClassicalFifthRational.value]

@[simp] theorem cast_initialValue (s : ℚ) :
    (initialValue s : ℝ) = ClassicalFifthRational.initialValue (s : ℝ) := by
  simp [initialValue, ClassicalFifthRational.initialValue, ClassicalSixthBranch.v, ClassicalSixthBranch.R, ClassicalSixthBranch.r]

@[simp] theorem cast_middleValue (s : ℚ) :
    (middleValue s : ℝ) = ClassicalFifthRational.middleValue (s : ℝ) := by
  simp [middleValue, ClassicalFifthRational.middleValue, ClassicalSixthBranch.v, ClassicalSixthBranch.R, ClassicalSixthBranch.r]

@[simp] theorem cast_terminalValue (s : ℚ) :
    (terminalValue s : ℝ) = ClassicalFifthRational.terminalValue (s : ℝ) := by
  simp [terminalValue, ClassicalFifthRational.terminalValue, ClassicalSixthBranch.u, ClassicalSixthBranch.R]

def initialCondition (q : ℕ → ℕ) (i : ℕ) : Prop :=
  (q i : ℚ)/1000000000000 ≤ initialValue (midpoint lo 4 1024 i)

theorem initialCondition_sound {q : ℕ → ℕ} {i : ℕ} (h : initialCondition q i) :
    (q i : ℝ)/1000000000000 ≤ ClassicalFifthRational.initialValue
      ((ClassicalUniformMidpoint.point ClassicalFifthSource.lo 4 1024 i +
        ClassicalUniformMidpoint.point ClassicalFifthSource.lo 4 1024 (i+1))/2) := by
  have hh := Rat.cast_le (K := ℝ) |>.mpr h
  simpa [ExactRational.midpoint, lo, ClassicalFifthSource.lo, WuSource.SrcSixthGain.split, QuarterTrim.alpha, QuarterTrim.beta,
    ClassicalUniformMidpoint.point, ClassicalUniformMidpoint.step] using hh

def middleCondition (q : ℕ → ℕ) (i : ℕ) : Prop :=
  (q i : ℚ)/1000000000000 ≤ middleValue (midpoint 4 cut 1024 i)

theorem middleCondition_sound {q : ℕ → ℕ} {i : ℕ} (h : middleCondition q i) :
    (q i : ℝ)/1000000000000 ≤ ClassicalFifthRational.middleValue
      ((ClassicalUniformMidpoint.point 4 ClassicalFifthSource.cut 1024 i +
        ClassicalUniformMidpoint.point 4 ClassicalFifthSource.cut 1024 (i+1))/2) := by
  have hh := Rat.cast_le (K := ℝ) |>.mpr h
  simpa [ExactRational.midpoint, cut, ClassicalFifthSource.cut, WuSource.SrcSixthGain.endpoint, QuarterTrim.alpha, QuarterTrim.beta,
    ClassicalUniformMidpoint.point, ClassicalUniformMidpoint.step] using hh

def terminalCondition (q : ℕ → ℕ) (i : ℕ) : Prop :=
  (q i : ℚ)/1000000000000 ≤ terminalValue (midpoint cut hi 1024 i)

theorem terminalCondition_sound {q : ℕ → ℕ} {i : ℕ} (h : terminalCondition q i) :
    (q i : ℝ)/1000000000000 ≤ ClassicalFifthRational.terminalValue
      ((ClassicalUniformMidpoint.point ClassicalFifthSource.cut ClassicalFifthSource.hi 1024 i +
        ClassicalUniformMidpoint.point ClassicalFifthSource.cut ClassicalFifthSource.hi 1024 (i+1))/2) := by
  have hh := Rat.cast_le (K := ℝ) |>.mpr h
  simpa [ExactRational.midpoint, cut, hi, ClassicalFifthSource.cut, ClassicalFifthSource.hi, WuSource.SrcSixthGain.endpoint, ClassicalFifthBranch.endpoint, ClassicalSixthBranch.R, QuarterTrim.alpha, QuarterTrim.beta,
    ClassicalUniformMidpoint.point, ClassicalUniformMidpoint.step] using hh

end WuPaper.ClassicalFifthTableCheck
