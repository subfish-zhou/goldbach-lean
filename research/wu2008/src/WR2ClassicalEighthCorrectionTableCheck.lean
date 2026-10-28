import WR2ClassicalEighthCorrectionPayments
import WR2ExactRationalLog

/-! The affine cell integral is evaluated once in exact rational arithmetic.
All original grid points, logarithm terms and stored payments are retained. -/
namespace WuPaper.ClassicalEighthCorrection.TableCheck

def qstep : ℚ := (1/10-100/1327)/512
def qpoint (i : ℕ) : ℚ := 100/1327+qstep*i
def qcell (l r : ℚ) : ℚ :=
  (r-l)*(1/10-(l+r)/2)*(ExactRational.logLo (2-3*r)/(r*(1-l)^2))
def condition (i : ℕ) : Prop :=
  qstep*((numerator i:ℚ)/1000000000000) ≤ qcell (qpoint i) (qpoint (i+1))
instance (i : ℕ) : Decidable (condition i) := inferInstanceAs (Decidable (_ ≤ _))

@[simp] theorem cast_step : (qstep:ℝ) = step := by
  simp [qstep,step,a,b,OriginalU8.SymbolicSmallGain.a,OriginalU8.SymbolicSmallGain.b]
@[simp] theorem cast_point (i : ℕ) : (qpoint i:ℝ) = point i := by
  simp [qpoint,point,a,OriginalU8.SymbolicSmallGain.a]
@[simp] theorem cast_cell (l r : ℚ) : (qcell l r:ℝ) = cellPayment l r := by
  simp [qcell,cellPayment,cellCoefficient,b,OriginalU8.SymbolicSmallGain.b]

theorem condition_sound {i : ℕ} (h : condition i) :
    step*payment i ≤ cellPayment (point i) (point (i+1)) := by
  have hh := (Rat.cast_le (K:=ℝ)).mpr h
  simpa [payment] using hh

end WuPaper.ClassicalEighthCorrection.TableCheck
#print axioms WuPaper.ClassicalEighthCorrection.TableCheck.condition_sound
