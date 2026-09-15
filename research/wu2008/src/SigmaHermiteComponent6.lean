import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set

def component6Kernel (t : ℝ) : ℝ := ((((448354787778360/315124733)+(115392069589572/315124733)*TerminalE.radical))+(((94815533250150/45017819)+(72926716295023/135053457)*TerminalE.radical))*t+(((-48138041624830/315124733)+(-41084992382411/945374199)*TerminalE.radical))*t^2+(((-49069894840040/28647703)+(-114021512659564/257829327)*TerminalE.radical))*t^3+(((-51303275480/42483)+(-39278583100/127449)*TerminalE.radical))*t^4+(((-158018744438540/405160371)+(-39402410283146/405160371)*TerminalE.radical))*t^5+(((-76378329366100/1215481113)+(-5943087951554/405160371)*TerminalE.radical))*t^6+(((-28638383085640/8508367791)+(-4364633774236/8508367791)*TerminalE.radical))*t^7+(((518476759840/1215481113)+(168437325136/1215481113)*TerminalE.radical))*t^8+(((654999508510/8508367791)+(142040899465/8508367791)*TerminalE.radical))*t^9+(((997739590/257829327)+(342491167/773487981)*TerminalE.radical))*t^10)/((block0.eval t)*(block3.eval t)^2*(block5.eval t)^4*(block10.eval t)*(block14.eval t))

def component6HermiteKernel (t : ℝ) : ℝ :=
  (0)+
  ((0)*(block3.eval t)-1*(((0+(-1504/11907)*TerminalE.radical)))*((1)))/(block3.eval t)^2+
  ((0)*(block5.eval t)-3*((((2364007120732160000/4727887604090268849)+(22794067419136000/175106948299639587)*TerminalE.radical)))*((1)))/(block5.eval t)^4+
  ((0)*(block5.eval t)-2*((((105473794639166777344000/89705548844831087532441)+(25663584480380254208000/89705548844831087532441)*TerminalE.radical)))*((1)))/(block5.eval t)^3+
  ((0)*(block5.eval t)-1*((((2943470402352542207398912000/5106140099390612078267901507)+(1286446725059766562102784000/5106140099390612078267901507)*TerminalE.radical)))*((1)))/(block5.eval t)^2+
  ((((-184862072866820/113827350837501)+(56094807438826/1024446157537509)*TerminalE.radical)))/(block0.eval t)+
  ((((-71440/27783)+(-608/27783)*TerminalE.radical)))/(block3.eval t)+
  ((((359112744240400958043733712384000/290647201319777664296743488491889)+(4167200998603768189767899648000/32294133479975296032971498721321)*TerminalE.radical)))/(block5.eval t)+
  ((((-420080266540122550341735583370/83519005445871961870980471627)+(10429893065363376221444954827/27839668481957320623660157209)*TerminalE.radical))+(((-15625244038198045724991057910/83519005445871961870980471627)+(-27893200013630484027704065511/250557016337615885612941414881)*TerminalE.radical))*t)/(block10.eval t)+
  ((((15187127927552281000000/372417960487462127469)+(3088339519064584000000/372417960487462127469)*TerminalE.radical))+(((13974047285837000000/1991539895654877687)+(2343254407016000000/5974619686964633061)*TerminalE.radical))*t)/(block14.eval t)

theorem component6_hermite {t : ℝ} (ht : t ∈ Icc 1 3) :
    component6Kernel t = component6HermiteKernel t := by
  have h0 := block0_eval_ne ht
  have h3 := block3_eval_ne ht
  have h5 := block5_eval_ne ht
  have h10 := block10_eval_ne ht
  have h14 := block14_eval_ne ht
  unfold component6Kernel component6HermiteKernel
  field_simp [h0, h3, h5, h10, h14]
  simp only [block0, block3, block5, block10, block14, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  have hr3 : TerminalE.radical^3 = 15*TerminalE.radical := by simpa using radical_power_reduce 1
  have hr4 : TerminalE.radical^4 = 15*TerminalE.radical^2 := radical_power_reduce 2
  have hr5 : TerminalE.radical^5 = 15*TerminalE.radical^3 := radical_power_reduce 3
  have hr6 : TerminalE.radical^6 = 15*TerminalE.radical^4 := radical_power_reduce 4
  ring_nf
  simp only [hr6, hr5, hr4, hr3, TerminalE.radical_sq]
  ring

end SigmaHermiteActualFTC
