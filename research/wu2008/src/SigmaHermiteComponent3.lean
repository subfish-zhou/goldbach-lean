import SigmaHermiteBlocks

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set

def component3Kernel (t : ℝ) : ℝ := (((-8388608/49))*t+((-76546048/147))*t^2+((-160694272/6615))*t^3+((20166443008/19845))*t^4+((-116207908864/59535))*t^5+((-4829944576/441))*t^6+((-12132910026112/694575))*t^7+((-13592064082232/1148175))*t^8+((127043907066032/56260575))*t^9+((423468259626232/33756345))*t^10+((2246635195046096/168781725))*t^11+((478157819250176/56260575))*t^12+((70504072775072/18753525))*t^13+((22556737823024/18753525))*t^14+((90424525472/321489))*t^15+((2681467699528/56260575))*t^16+((106814201552/18753525))*t^17+((2842229608/6251175))*t^18+((3667389328/168781725))*t^19+((15846032/33756345))*t^20)/((block0.eval t)^5*(block2.eval t)^2*(block3.eval t)^2*(block11.eval t)^4*(block16.eval t))

def component3HermiteKernel (t : ℝ) : ℝ :=
  (0)+
  ((0)*(block0.eval t)-4*(0)*((1)))/(block0.eval t)^5+
  ((0)*(block0.eval t)-3*(((16/2835)))*((1)))/(block0.eval t)^4+
  ((0)*(block0.eval t)-2*(((-31/945)))*((1)))/(block0.eval t)^3+
  ((0)*(block0.eval t)-1*(((2131/25515)))*((1)))/(block0.eval t)^2+
  ((0)*(block2.eval t)-1*(((-3/175)))*((1)))/(block2.eval t)^2+
  ((0)*(block3.eval t)-1*(((-2048/18225)))*((1)))/(block3.eval t)^2+
  ((((184188896/409898475)))*(block11.eval t)-3*(((22708768/35134155))+((184188896/409898475))*t)*((7)+(2)*t))/(block11.eval t)^4+
  ((((-53150086/142209675)))*(block11.eval t)-2*(((-4504313242/6968274075))+((-53150086/142209675))*t)*((7)+(2)*t))/(block11.eval t)^3+
  ((((1032395153/8774863650)))*(block11.eval t)-1*(((2527043705/9476852742))+((1032395153/8774863650))*t)*((7)+(2)*t))/(block11.eval t)^2+
  (((-17263/408240)))/(block0.eval t)+
  (((127/22050)))/(block2.eval t)+
  (((-9472/42525)))/(block3.eval t)+
  (((7571714713/38681031600))+((46746967/385786800))*t)/(block11.eval t)+
  (((6562789/750141))+((21810826/1607445))*t+((9723493/1607445))*t^2+((6835852/11252115))*t^3)/(block16.eval t)

theorem component3_hermite {t : ℝ} (ht : t ∈ Icc 1 3) :
    component3Kernel t = component3HermiteKernel t := by
  have h0 := block0_eval_ne ht
  have h2 := block2_eval_ne ht
  have h3 := block3_eval_ne ht
  have h11 := block11_eval_ne ht
  have h16 := block16_eval_ne ht
  unfold component3Kernel component3HermiteKernel
  field_simp [h0, h2, h3, h11, h16]
  simp only [block0, block2, block3, block11, block16, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

end SigmaHermiteActualFTC
