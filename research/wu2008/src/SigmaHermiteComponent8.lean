import SigmaHermiteBlocks

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set

def component8Kernel (t : ℝ) : ℝ := (((32/35))+((-184/105))*t+((-1144/945))*t^2+((-5261/540))*t^3+((176/63))*t^4+((1759/270))*t^5+((2122/945))*t^6+((299/1260))*t^7)/((block0.eval t)^4*(block1.eval t)*(block3.eval t)^3)

def component8HermiteKernel (t : ℝ) : ℝ :=
  (0)+
  ((0)*(block0.eval t)-3*(((-32/2835)))*((1)))/(block0.eval t)^4+
  ((0)*(block0.eval t)-2*(((188/2835)))*((1)))/(block0.eval t)^3+
  ((0)*(block0.eval t)-1*(((-4472/25515)))*((1)))/(block0.eval t)^2+
  ((0)*(block3.eval t)-2*(((512/8505)))*((1)))/(block3.eval t)^3+
  ((0)*(block3.eval t)-1*(((8192/25515)))*((1)))/(block3.eval t)^2+
  (((-11167/20412)))/(block0.eval t)+
  (((83/70)))/(block1.eval t)+
  (((-2048/5103)))/(block3.eval t)

theorem component8_hermite {t : ℝ} (ht : t ∈ Icc 1 3) :
    component8Kernel t = component8HermiteKernel t := by
  have h0 := block0_eval_ne ht
  have h1 := block1_eval_ne ht
  have h3 := block3_eval_ne ht
  unfold component8Kernel component8HermiteKernel
  field_simp [h0, h1, h3]
  simp only [block0, block1, block3, eval_add, eval_mul, eval_X, eval_C]
  ring

end SigmaHermiteActualFTC
