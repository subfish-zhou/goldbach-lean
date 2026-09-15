import SigmaHermiteBlocks

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set

def component2Kernel (t : ℝ) : ℝ := (((-8153726976/7))*t+((-29557260288/7))*t^2+((-39758856192/35))*t^3+((341638250496/35))*t^4+((-369194819584/35))*t^5+((-9362386895872/105))*t^6+((-1614741497924096/11025))*t^7+((-2761988230732576/33075))*t^8+((548938408808896/11025))*t^9+((11973108494440096/99225))*t^10+((9598264293025984/99225))*t^11+((487361650776064/11025))*t^12+((414453113564288/33075))*t^13+((74204065476032/33075))*t^14+((2831080249216/11025))*t^15+((624006729952/33075))*t^16+((29052831296/33075))*t^17+((30431264/1225))*t^18+((7658176/19845))*t^19+((9920/3969))*t^20)/((block0.eval t)^5*(block12.eval t)^2*(block15.eval t)^4*(block20.eval t))

def component2HermiteKernel (t : ℝ) : ℝ :=
  (0)+
  ((0)*(block0.eval t)-4*(0)*((1)))/(block0.eval t)^5+
  ((0)*(block0.eval t)-3*(((16/2835)))*((1)))/(block0.eval t)^4+
  ((0)*(block0.eval t)-2*(((-19/567)))*((1)))/(block0.eval t)^3+
  ((0)*(block0.eval t)-1*(((2341/25515)))*((1)))/(block0.eval t)^2+
  ((((-5323127/18625950)))*(block12.eval t)-1*(((-6513937/18625950))+((-5323127/18625950))*t)*((11)+(2)*t))/(block12.eval t)^2+
  ((((970711791904/55239975)))*(block15.eval t)-3*(((7445085461024/386679825))+((970711791904/55239975))*t)*((23)+(2)*t))/(block15.eval t)^4+
  ((((-763091222978/3416987025)))*(block15.eval t)-2*(((-182363071457822/167432364225))+((-763091222978/3416987025))*t)*((23)+(2)*t))/(block15.eval t)^3+
  ((((206458531618559/260993569353930)))*(block15.eval t)-1*(((17677381714937753/1304967846769650))+((206458531618559/260993569353930))*t)*((23)+(2)*t))/(block15.eval t)^2+
  (((-8993/408240)))/(block0.eval t)+
  (((-19515919/34768440))+((-969637/2381400))*t)/(block12.eval t)+
  (((2795622945448517/6263845664494320))+((148536839/385786800))*t)/(block15.eval t)+
  (((15374879/107163))+((4849797857/19289340))*t+((1073189653/9644670))*t^2+((49063337/19289340))*t^3)/(block20.eval t)

theorem component2_hermite {t : ℝ} (ht : t ∈ Icc 1 3) :
    component2Kernel t = component2HermiteKernel t := by
  have h0 := block0_eval_ne ht
  have h12 := block12_eval_ne ht
  have h15 := block15_eval_ne ht
  have h20 := block20_eval_ne ht
  unfold component2Kernel component2HermiteKernel
  field_simp [h0, h12, h15, h20]
  simp only [block0, block12, block15, block20, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

end SigmaHermiteActualFTC
