import Wu04FullPsiSharp
import JointLogTotalComparison

namespace Wu04FullPsiEndpoints
open Wu2008DoubleSieve Wu04FullPsiSharp SharpLogRecurrence JointLogTotalComparison Real
noncomputable section

def rationalJ (B A : ℝ) : ℝ :=
  c A*lowerLog ((A-1)/(B-1)) +
  d A*(1/(1-1/A)-1/(1-1/B)) +
  Wu04FullPsiSharp.e A*(1/(1-1/A)^2-1/(1-1/B)^2) +
  f A*(1/(1-1/A)^3-1/(1-1/B)^3)

theorem log_endpoint {A : ℝ} (hA : 1 < A) :
    log (1-1/A)-log (1/A) = log (A-1) := by
  have hA0 : 0 < A := by linarith
  have hi : 0 < 1-1/A := by
    apply sub_pos.mpr
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) hA
  rw [← log_div hi.ne' (one_div_ne_zero hA0.ne')]
  congr 1
  field_simp

theorem lowerJ_closed {A B : ℝ} (hA : 1 < A) (hB : 1 < B) :
    lowerJ B A = c A*log ((A-1)/(B-1)) +
      d A*(1/(1-1/A)-1/(1-1/B)) +
      Wu04FullPsiSharp.e A*(1/(1-1/A)^2-1/(1-1/B)^2) +
      f A*(1/(1-1/A)^3-1/(1-1/B)^3) := by
  unfold lowerJ primitive
  rw [show 1-(1-1/A)=1/A by ring, show 1-(1-1/B)=1/B by ring,
    log_endpoint hA, log_endpoint hB,
    log_div (by linarith : A-1 ≠ 0) (by linarith : B-1 ≠ 0)]
  ring

theorem rationalJ_le {A B : ℝ} (hB : 2 < B) (hBA : B ≤ A)
    (hc : 0 ≤ c A) : rationalJ B A ≤ lowerJ B A := by
  rw [lowerJ_closed (by linarith) (by linarith)]
  have hr : 1 ≤ (A-1)/(B-1) := (one_le_div (by linarith)).2 (by linarith)
  have h := mul_le_mul_of_nonneg_left (log_lower hr) hc
  unfold rationalJ
  linarith only [h]

def rationalL (A : ℝ) : ℝ :=
  (A-3)/6-lowerLog (A-2)/6+(4/3)*V ((A-1)/2)+8/(3*(A-1))-4/3

theorem upperL_closed {A : ℝ} (hA : 3 ≤ A) :
    upperL A = (A-3)/6-log (A-2)/6+(4/3)*log ((A-1)/2)+8/(3*(A-1))-4/3 := by
  unfold upperL upperPrimitive
  rw [log_div (by linarith : A-1 ≠ 0) (by norm_num : (2:ℝ)≠0)]
  rw [show A-1-1=A-2 by ring]
  norm_num
  ring

theorem upperL_le {A : ℝ} (hA : 3 ≤ A) : upperL A ≤ rationalL A := by
  rw [upperL_closed hA]
  have h1 := log_lower (by linarith : (1:ℝ)≤A-2)
  have h2 := log_le_V (show (1:ℝ)≤(A-1)/2 by linarith)
  unfold rationalL
  linarith only [h1,h2]

#print axioms rationalJ_le
#print axioms upperL_le
end
end Wu04FullPsiEndpoints
