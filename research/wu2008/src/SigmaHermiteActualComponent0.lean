import SigmaHermiteComponent0
import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set SigmaRationalOuterFTC

def actual0Scale : ℝ := 264600
def actual0Numerator (t : ℝ) : ℝ := (-(2145*t^2+4418*t+2280))*upperNum (t+2+(3)) (2*(3))
def actual0Denominator (t : ℝ) : ℝ := (210*(t+1)^2)*upperDen (t+2+(3)) (2*(3))*t
def actual0Weight (t : ℝ) : ℝ := (-(2145*t^2+4418*t+2280))/(210*(t+1)^2)*(upperNum (t+2+(3)) (2*(3))/upperDen (t+2+(3)) (2*(3)))/t

theorem actual0_scale_ne : actual0Scale ≠ 0 := by
  norm_num [actual0Scale]

theorem actual0_num_identity (t : ℝ) : actual0Numerator t = actual0Scale*(((532539296/735))+((12816032354/11025))*t+((-351559743/2450))*t^2+((-2160709751/2100))*t^3+((-177538607/315))*t^4+((-11221193/84))*t^5+((-17140243/1050))*t^6+((-45774541/44100))*t^7+((-108712/3675))*t^8+((-143/980))*t^9) := by
  unfold actual0Numerator actual0Scale upperNum
  ring

theorem actual0_den_identity (t : ℝ) : actual0Denominator t = actual0Scale*((block0.eval t)*(block1.eval t)^2*(block6.eval t)^2*(block9.eval t)^4) := by
  unfold actual0Denominator actual0Scale upperDen
  simp only [block0, block1, block6, block9, eval_add, eval_mul, eval_X, eval_C]
  ring

theorem actual0_weight_kernel (t : ℝ) : actual0Weight t = component0Kernel t := by
  have he : actual0Weight t = actual0Numerator t/actual0Denominator t := by
    unfold actual0Weight actual0Numerator actual0Denominator
    simp only [div_mul_div_comm, div_div]
  rw [he, actual0_num_identity, actual0_den_identity]
  exact mul_div_mul_left _ _ actual0_scale_ne

end SigmaHermiteActualFTC
