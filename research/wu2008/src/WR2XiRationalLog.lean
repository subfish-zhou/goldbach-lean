import WR2XiProductPanels
import Mathlib.Data.Rat.Cast.Order

/-! Computable rational logarithm bounds with an explicit real-cast bridge. -/
namespace WuPaper.R2Xi
open Wu2008DoubleSieve Wu04FactorEnvelopes

def rationalBasicLog (x : ℚ) : ℚ :=
  let y := (x - 1) / (x + 1)
  2*y + 2*y^3/3

def rationalFactorLog (x : ℚ) : ℚ :=
  rationalBasicLog ((1+x)/2) + rationalBasicLog (2*x/(1+x))

def rationalCellLog (x : ℚ) : ℚ :=
  rationalFactorLog ((1+x)/2) + rationalFactorLog (2*x/(1+x))

theorem rationalBasicLog_cast (x : ℚ) :
    (rationalBasicLog x : ℝ) = SharpLogRecurrence.lowerLog (x : ℝ) := by
  unfold rationalBasicLog SharpLogRecurrence.lowerLog
  push_cast
  rfl

theorem rationalFactorLog_cast (x : ℚ) :
    (rationalFactorLog x : ℝ) = lower (x : ℝ) := by
  unfold rationalFactorLog lower
  rw [Rat.cast_add, rationalBasicLog_cast, rationalBasicLog_cast]
  unfold leftFactor rightFactor
  push_cast
  rfl

theorem rationalCellLog_cast (x : ℚ) :
    (rationalCellLog x : ℝ) = cellLogLower (x : ℝ) := by
  unfold rationalCellLog cellLogLower
  rw [Rat.cast_add, rationalFactorLog_cast, rationalFactorLog_cast]
  unfold leftFactor rightFactor
  push_cast
  rfl

open scoped BigOperators

def rationalProductLog {n : ℕ} (q : Fin n → ℚ) (a : ℚ) : ℚ :=
  ∑ j, rationalCellLog ((a + 1) / q j)

theorem rationalProductLog_cast {n : ℕ} (q : Fin n → ℚ) (a : ℚ) :
    (rationalProductLog q a : ℝ) = productLogLower (fun j => (q j : ℝ)) (a : ℝ) := by
  unfold rationalProductLog productLogLower
  push_cast
  simp_rw [rationalCellLog_cast]
  push_cast
  rfl

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.rationalCellLog_cast

#print axioms WuPaper.R2Xi.rationalProductLog_cast
