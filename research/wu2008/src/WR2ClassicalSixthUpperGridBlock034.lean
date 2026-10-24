import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints034
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_034 (j : Fin 16) : upperPayment (16*34+j.val) ≤
    upperValue ((point split endpoint 4096 (16*34+j.val)+point split endpoint 4096 (16*34+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 544 ≤ upperValue ((point split endpoint 4096 544+point split endpoint 4096 545)/2)
    have hp : upperPayment 544 = (391953349721:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 544+point split endpoint 4096 545)/2 = (589845727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589845727:ℝ)/168755200)*ClassicalSixthBranch.v ((589845727:ℝ)/168755200)/ClassicalSixthBranch.r = (149101456080081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_544
  · change upperPayment 545 ≤ upperValue ((point split endpoint 4096 545+point split endpoint 4096 546)/2)
    have hp : upperPayment 545 = (391888451461:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 545+point split endpoint 4096 546)/2 = (589870877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589870877:ℝ)/168755200)*ClassicalSixthBranch.v ((589870877:ℝ)/168755200)/ClassicalSixthBranch.r = (149076541882457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_545
  · change upperPayment 546 ≤ upperValue ((point split endpoint 4096 546+point split endpoint 4096 547)/2)
    have hp : upperPayment 546 = (391823532628:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 546+point split endpoint 4096 547)/2 = (589896027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589896027:ℝ)/168755200)*ClassicalSixthBranch.v ((589896027:ℝ)/168755200)/ClassicalSixthBranch.r = (149051629708905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_546
  · change upperPayment 547 ≤ upperValue ((point split endpoint 4096 547+point split endpoint 4096 548)/2)
    have hp : upperPayment 547 = (391758593220:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 547+point split endpoint 4096 548)/2 = (589921177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589921177:ℝ)/168755200)*ClassicalSixthBranch.v ((589921177:ℝ)/168755200)/ClassicalSixthBranch.r = (149026719559425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_547
  · change upperPayment 548 ≤ upperValue ((point split endpoint 4096 548+point split endpoint 4096 549)/2)
    have hp : upperPayment 548 = (391693633235:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 548+point split endpoint 4096 549)/2 = (589946327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589946327:ℝ)/168755200)*ClassicalSixthBranch.v ((589946327:ℝ)/168755200)/ClassicalSixthBranch.r = (149001811434017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_548
  · change upperPayment 549 ≤ upperValue ((point split endpoint 4096 549+point split endpoint 4096 550)/2)
    have hp : upperPayment 549 = (391628652668:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 549+point split endpoint 4096 550)/2 = (589971477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589971477:ℝ)/168755200)*ClassicalSixthBranch.v ((589971477:ℝ)/168755200)/ClassicalSixthBranch.r = (148976905332681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_549
  · change upperPayment 550 ≤ upperValue ((point split endpoint 4096 550+point split endpoint 4096 551)/2)
    have hp : upperPayment 550 = (391563651519:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 550+point split endpoint 4096 551)/2 = (589996627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589996627:ℝ)/168755200)*ClassicalSixthBranch.v ((589996627:ℝ)/168755200)/ClassicalSixthBranch.r = (148952001255417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_550
  · change upperPayment 551 ≤ upperValue ((point split endpoint 4096 551+point split endpoint 4096 552)/2)
    have hp : upperPayment 551 = (391498629782:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 551+point split endpoint 4096 552)/2 = (590021777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590021777:ℝ)/168755200)*ClassicalSixthBranch.v ((590021777:ℝ)/168755200)/ClassicalSixthBranch.r = (148927099202225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_551
  · change upperPayment 552 ≤ upperValue ((point split endpoint 4096 552+point split endpoint 4096 553)/2)
    have hp : upperPayment 552 = (391433587457:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 552+point split endpoint 4096 553)/2 = (590046927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590046927:ℝ)/168755200)*ClassicalSixthBranch.v ((590046927:ℝ)/168755200)/ClassicalSixthBranch.r = (148902199173105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_552
  · change upperPayment 553 ≤ upperValue ((point split endpoint 4096 553+point split endpoint 4096 554)/2)
    have hp : upperPayment 553 = (391368524540:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 553+point split endpoint 4096 554)/2 = (590072077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590072077:ℝ)/168755200)*ClassicalSixthBranch.v ((590072077:ℝ)/168755200)/ClassicalSixthBranch.r = (148877301168057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_553
  · change upperPayment 554 ≤ upperValue ((point split endpoint 4096 554+point split endpoint 4096 555)/2)
    have hp : upperPayment 554 = (391303441029:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 554+point split endpoint 4096 555)/2 = (590097227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590097227:ℝ)/168755200)*ClassicalSixthBranch.v ((590097227:ℝ)/168755200)/ClassicalSixthBranch.r = (148852405187081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_554
  · change upperPayment 555 ≤ upperValue ((point split endpoint 4096 555+point split endpoint 4096 556)/2)
    have hp : upperPayment 555 = (391238336920:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 555+point split endpoint 4096 556)/2 = (590122377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590122377:ℝ)/168755200)*ClassicalSixthBranch.v ((590122377:ℝ)/168755200)/ClassicalSixthBranch.r = (148827511230177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_555
  · change upperPayment 556 ≤ upperValue ((point split endpoint 4096 556+point split endpoint 4096 557)/2)
    have hp : upperPayment 556 = (391173212210:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 556+point split endpoint 4096 557)/2 = (590147527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590147527:ℝ)/168755200)*ClassicalSixthBranch.v ((590147527:ℝ)/168755200)/ClassicalSixthBranch.r = (148802619297345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_556
  · change upperPayment 557 ≤ upperValue ((point split endpoint 4096 557+point split endpoint 4096 558)/2)
    have hp : upperPayment 557 = (391108066898:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 557+point split endpoint 4096 558)/2 = (590172677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590172677:ℝ)/168755200)*ClassicalSixthBranch.v ((590172677:ℝ)/168755200)/ClassicalSixthBranch.r = (148777729388585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_557
  · change upperPayment 558 ≤ upperValue ((point split endpoint 4096 558+point split endpoint 4096 559)/2)
    have hp : upperPayment 558 = (391042900980:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 558+point split endpoint 4096 559)/2 = (590197827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590197827:ℝ)/168755200)*ClassicalSixthBranch.v ((590197827:ℝ)/168755200)/ClassicalSixthBranch.r = (148752841503897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_558
  · change upperPayment 559 ≤ upperValue ((point split endpoint 4096 559+point split endpoint 4096 560)/2)
    have hp : upperPayment 559 = (390977714454:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 559+point split endpoint 4096 560)/2 = (590222977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590222977:ℝ)/168755200)*ClassicalSixthBranch.v ((590222977:ℝ)/168755200)/ClassicalSixthBranch.r = (148727955643281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_559
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_034
