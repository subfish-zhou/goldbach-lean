import SigmaHermiteBlocks

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set

def component1Kernel (t : ℝ) : ℝ := (((155774369/39690))+((29222898239/2381400))*t+((56562815341/4762800))*t^2+((-304537777/226800))*t^3+((-1550445049/136080))*t^4+((-192279589/19440))*t^5+((-323095391/75600))*t^6+((-4911803591/4762800))*t^7+((-631631993/4762800))*t^8+((-2248103/317520))*t^9)/((block0.eval t)*(block1.eval t)^2*(block2.eval t)^2*(block3.eval t)^4*(block6.eval t))

def component1HermiteKernel (t : ℝ) : ℝ :=
  (0)+
  ((0)*(block1.eval t)-1*(((131/5670)))*((1)))/(block1.eval t)^2+
  ((0)*(block2.eval t)-1*(((-759/4900)))*((1)))/(block2.eval t)^2+
  ((0)*(block3.eval t)-3*(((-355456/893025)))*((1)))/(block3.eval t)^4+
  ((0)*(block3.eval t)-2*(((896384/893025)))*((1)))/(block3.eval t)^3+
  ((0)*(block3.eval t)-1*(((-5475584/2679075)))*((1)))/(block3.eval t)^2+
  (((155774369/64297800)))/(block0.eval t)+
  (((-400633/952560)))/(block1.eval t)+
  (((-4723/2800)))/(block2.eval t)+
  (((-51119728/8037225)))/(block3.eval t)+
  (((-20289/19600)))/(block6.eval t)

theorem component1_hermite {t : ℝ} (ht : t ∈ Icc 1 3) :
    component1Kernel t = component1HermiteKernel t := by
  have h0 := block0_eval_ne ht
  have h1 := block1_eval_ne ht
  have h2 := block2_eval_ne ht
  have h3 := block3_eval_ne ht
  have h6 := block6_eval_ne ht
  unfold component1Kernel component1HermiteKernel
  field_simp [h0, h1, h2, h3, h6]
  simp only [block0, block1, block2, block3, block6, eval_add, eval_mul, eval_X, eval_C]
  ring

end SigmaHermiteActualFTC
