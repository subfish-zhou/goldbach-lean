import SigmaHermiteComponent1
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set SigmaRationalOuterFTC

def actual1Scale : ℝ := 14288400
def actual1Numerator (t : ℝ) : ℝ := (-(2145*t^2+4418*t+2280))*upperNum (2*(t+2)) (t+2+(3))
def actual1Denominator (t : ℝ) : ℝ := (210*(t+1)^2)*upperDen (2*(t+2)) (t+2+(3))*t
def actual1Weight (t : ℝ) : ℝ := (-(2145*t^2+4418*t+2280))/(210*(t+1)^2)*(upperNum (2*(t+2)) (t+2+(3))/upperDen (2*(t+2)) (t+2+(3)))/t

theorem actual1_scale_ne : actual1Scale ≠ 0 := by
  norm_num [actual1Scale]

theorem actual1_num_identity (t : ℝ) : actual1Numerator t = actual1Scale*(((155774369/39690))+((29222898239/2381400))*t+((56562815341/4762800))*t^2+((-304537777/226800))*t^3+((-1550445049/136080))*t^4+((-192279589/19440))*t^5+((-323095391/75600))*t^6+((-4911803591/4762800))*t^7+((-631631993/4762800))*t^8+((-2248103/317520))*t^9) := by
  unfold actual1Numerator actual1Scale upperNum
  ring

theorem actual1_den_identity (t : ℝ) : actual1Denominator t = actual1Scale*((block0.eval t)*(block1.eval t)^2*(block2.eval t)^2*(block3.eval t)^4*(block6.eval t)) := by
  unfold actual1Denominator actual1Scale upperDen
  simp only [block0, block1, block2, block3, block6, eval_add, eval_mul, eval_X, eval_C]
  ring

theorem actual1_weight_kernel (t : ℝ) : actual1Weight t = component1Kernel t := by
  have he : actual1Weight t = actual1Numerator t/actual1Denominator t := by
    unfold actual1Weight actual1Numerator actual1Denominator
    simp only [div_mul_div_comm, div_div]
  rw [he, actual1_num_identity, actual1_den_identity]
  exact mul_div_mul_left _ _ actual1_scale_ne

end SigmaHermiteActualFTC
