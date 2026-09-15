import SigmaHermiteRadicalReduction

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set

def component7Kernel (t : ℝ) : ℝ := ((((284647935100950/6431117)+(-514461163909500/45017819)*TerminalE.radical))+(((2359152189314275/57295406)+(-913621735233875/85943109)*TerminalE.radical))*t+(((-55585160603185625/1890748398)+(2392415196384625/315124733)*TerminalE.radical))*t^2+(((-36592060920933250/945374199)+(28345721359890500/2836122597)*TerminalE.radical))*t^3+(((-542582783715850/36832761)+(140067708857500/36832761)*TerminalE.radical))*t^4+(((-91497542537125/36832761)+(70741495702250/110498283)*TerminalE.radical))*t^5+(((-9597243014225/71498889)+(2423846285750/71498889)*TerminalE.radical))*t^6+(((18444005374250/1215481113)+(-561737493500/135053457)*TerminalE.radical))*t^7+(((22666304077000/8508367791)+(-6124931774000/8508367791)*TerminalE.radical))*t^8+(((2544927371075/17016735582)+(-317998500625/8508367791)*TerminalE.radical))*t^9+(((2013863975/515658654)+(-349618375/773487981)*TerminalE.radical))*t^10)/((block0.eval t)*(block4.eval t)^4*(block7.eval t)^2*(block10.eval t)*(block13.eval t))

def component7HermiteKernel (t : ℝ) : ℝ :=
  (0)+
  ((0)*(block4.eval t)-3*((((-2364007120732160000/4727887604090268849)+(22794067419136000/175106948299639587)*TerminalE.radical)))*((1)))/(block4.eval t)^4+
  ((0)*(block4.eval t)-2*((((162003511199503628288000/89705548844831087532441)+(-4504290509963970560000/9967283204981231948049)*TerminalE.radical)))*((1)))/(block4.eval t)^3+
  ((0)*(block4.eval t)-1*((((-11363620589124323686638592000/5106140099390612078267901507)+(3257643376802687477419110400/5106140099390612078267901507)*TerminalE.radical)))*((1)))/(block4.eval t)^2+
  ((0)*(block7.eval t)-1*((((7921000/512001)+(-685600/170667)*TerminalE.radical)))*((1)))/(block7.eval t)^2+
  ((((-26408869702675/16261050119643)+(-18698284054250/341482052512503)*TerminalE.radical)))/(block0.eval t)+
  ((((283368648799027705009269493043200/290647201319777664296743488491889)+(-4551523047275320836690259456000/290647201319777664296743488491889)*TerminalE.radical)))/(block4.eval t)+
  ((((-1929240700/462336903)+(310291000/462336903)*TerminalE.radical)))/(block7.eval t)+
  ((((-1555309463484225227332605300297425/308853282138834514998885784076646)+(-58093713599515496476740337377875/154426641069417257499442892038323)*TerminalE.radical))+(((-57517175705857397394713424628775/308853282138834514998885784076646)+(51680735844339533552970071867875/463279923208251772498328676114969)*TerminalE.radical))*t)/(block10.eval t)+
  ((((12598768997428259000000/372417960487462127469)+(-2279130327796216000000/372417960487462127469)*TerminalE.radical))+(((1972410269527000000/221282210628319743)+(-993729688912000000/853517098137804723)*TerminalE.radical))*t)/(block13.eval t)

theorem component7_hermite {t : ℝ} (ht : t ∈ Icc 1 3) :
    component7Kernel t = component7HermiteKernel t := by
  have h0 := block0_eval_ne ht
  have h4 := block4_eval_ne ht
  have h7 := block7_eval_ne ht
  have h10 := block10_eval_ne ht
  have h13 := block13_eval_ne ht
  unfold component7Kernel component7HermiteKernel
  field_simp [h0, h4, h7, h10, h13]
  simp only [block0, block4, block7, block10, block13, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  have hr3 : TerminalE.radical^3 = 15*TerminalE.radical^1 := radical_power_reduce 1
  have hr4 : TerminalE.radical^4 = 15*TerminalE.radical^2 := radical_power_reduce 2
  have hr5 : TerminalE.radical^5 = 15*TerminalE.radical^3 := radical_power_reduce 3
  have hr6 : TerminalE.radical^6 = 15*TerminalE.radical^4 := radical_power_reduce 4
  have hr7 : TerminalE.radical^7 = 15*TerminalE.radical^5 := radical_power_reduce 5
  have hr8 : TerminalE.radical^8 = 15*TerminalE.radical^6 := radical_power_reduce 6
  ring_nf
  simp only [hr8, hr7, hr6, hr5, hr4, hr3, TerminalE.radical_sq, pow_one]
  ring

end SigmaHermiteActualFTC
