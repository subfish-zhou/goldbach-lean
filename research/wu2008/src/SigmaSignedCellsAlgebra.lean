import SigmaPrimitiveCells
namespace SigmaSignedCells
open Real F1JointFTC
noncomputable section

def quadratic (t : ℝ) : ℝ := t^2+18*t+21
def conjugateRatio (a b : ℝ) : ℝ :=
  ((b+9-root)*(a+9+root))/((b+9+root)*(a+9-root))

theorem quadratic_pos {t : ℝ} (ht : 1≤t) : 0<quadratic t := by
  unfold quadratic
  positivity

theorem quadratic_ratio_ge {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    1≤quadratic b/quadratic a := by
  apply (one_le_div (quadratic_pos ha)).mpr
  unfold quadratic
  nlinarith only [ha,hab,sq_nonneg (b-a)]

theorem conjugateRatio_ge {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    1≤conjugateRatio a b := by
  have ham : 0<a+9-root := by linarith only [ha,root_lt_eight]
  have hbp : 0<b+9+root := by linarith only [ha,hab,root_pos]
  unfold conjugateRatio
  apply (one_le_div (mul_pos hbp ham)).mpr
  nlinarith only [mul_nonneg root_pos.le (sub_nonneg.mpr hab)]

theorem quadratic_collected (f g : ℝ) {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    SigmaInnerPaid.quadraticPrimitive f g b-SigmaInnerPaid.quadraticPrimitive f g a =
      (f/2)*log (quadratic b/quadratic a)+((g-9*f)/(2*root))*log (conjugateRatio a b) := by
  have hb : 1≤b := ha.trans hab
  have ham : 0<a+9-root := by linarith only [ha,root_lt_eight]
  have hbm : 0<b+9-root := by linarith only [hb,root_lt_eight]
  have hap : 0<a+9+root := by linarith only [ha,root_pos]
  have hbp : 0<b+9+root := by linarith only [hb,root_pos]
  have hq (t : ℝ) : (t+1)^2+16*(t+1)+4=quadratic t := by unfold quadratic; ring
  have ht (t : ℝ) : t+1+8=t+9 := by ring
  unfold SigmaInnerPaid.quadraticPrimitive F1JointFTC.quadraticPrimitive
  rw [hq a,hq b,ht a,ht b]
  rw [log_div (quadratic_pos hb).ne' (quadratic_pos ha).ne']
  unfold conjugateRatio
  rw [log_div (mul_pos hbm hap).ne' (mul_pos hbp ham).ne',
    log_mul hbm.ne' hap.ne',log_mul hbp.ne' ham.ne']
  ring

def quadraticPaid (f g a b : ℝ) : ℝ :=
  RemainingHf.signed (f/2) (quadratic b/quadratic a)+
    RemainingHf.signed ((g-9*f)/(2*root)) (conjugateRatio a b)

theorem quadraticPaid_le (f g : ℝ) {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    quadraticPaid f g a b ≤
      SigmaInnerPaid.quadraticPrimitive f g b-SigmaInnerPaid.quadraticPrimitive f g a := by
  rw [quadratic_collected f g ha hab]
  exact add_le_add (RemainingHf.signed_le _ (quadratic_ratio_ge ha hab))
    (RemainingHf.signed_le _ (conjugateRatio_ge ha hab))

end
end SigmaSignedCells
