import SigmaHermiteBlocks

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set

def component0Kernel (t : ℝ) : ℝ := (((532539296/735))+((12816032354/11025))*t+((-351559743/2450))*t^2+((-2160709751/2100))*t^3+((-177538607/315))*t^4+((-11221193/84))*t^5+((-17140243/1050))*t^6+((-45774541/44100))*t^7+((-108712/3675))*t^8+((-143/980))*t^9)/((block0.eval t)*(block1.eval t)^2*(block6.eval t)^2*(block9.eval t)^4)

def component0HermiteKernel (t : ℝ) : ℝ :=
  (((-143/980)))+
  ((0)*(block1.eval t)-1*(((212869/15750000)))*((1)))/(block1.eval t)^2+
  ((0)*(block6.eval t)-1*(((-20289/19600)))*((1)))/(block6.eval t)^2+
  ((0)*(block9.eval t)-3*(((-35091072/48125)))*((1)))/(block9.eval t)^4+
  ((0)*(block9.eval t)-2*(((7176459264/18528125)))*((1)))/(block9.eval t)^3+
  ((0)*(block9.eval t)-1*(((-114455383104/1019046875)))*((1)))/(block9.eval t)^2+
  (((532539296/269028375)))/(block0.eval t)+
  (((-92728571/367500000)))/(block1.eval t)+
  (((-568839/196000)))/(block6.eval t)+
  (((-23145358416/1143828125)))/(block9.eval t)

theorem component0_hermite {t : ℝ} (ht : t ∈ Icc 1 3) :
    component0Kernel t = component0HermiteKernel t := by
  have h0 := block0_eval_ne ht
  have h1 := block1_eval_ne ht
  have h6 := block6_eval_ne ht
  have h9 := block9_eval_ne ht
  unfold component0Kernel component0HermiteKernel
  field_simp [h0, h1, h6, h9]
  simp only [block0, block1, block6, block9, eval_add, eval_mul, eval_X, eval_C]
  ring

end SigmaHermiteActualFTC
