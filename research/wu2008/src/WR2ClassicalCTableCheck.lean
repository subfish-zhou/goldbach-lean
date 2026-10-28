import WR2ClassicalCUniform
import WR2ExactRationalLog

namespace WuPaper.ClassicalCTableCheck
open ExactRational

def splitLower (t : ℚ) : ℚ := logLo ((1+t)/2)+logLo (2*t/(1+t))
def value (u : ℚ) : ℚ := splitLower (u-1)/u*splitLower ((1327/200-1)/(u+1))

@[simp] theorem cast_splitLower (t : ℚ) :
    (splitLower t : ℝ) = ClassicalLogSplit.lower 1 (t : ℝ) := by
  simp [splitLower, ClassicalLogSplit.lower]

@[simp] theorem cast_value (u : ℚ) :
    (value u : ℝ) = ClassicalC.lowerKernel 1 (1327/200) (u : ℝ) := by
  simp [value, ClassicalC.lowerKernel]

end WuPaper.ClassicalCTableCheck
