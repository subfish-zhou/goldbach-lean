import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints037
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_037 (j : Fin 16) : upperPayment (16*37+j.val) ≤
    upperValue ((point split endpoint 4096 (16*37+j.val)+point split endpoint 4096 (16*37+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 592 ≤ upperValue ((point split endpoint 4096 592+point split endpoint 4096 593)/2)
    have hp : upperPayment 592 = (388814979328:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 592+point split endpoint 4096 593)/2 = (591052927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591052927:ℝ)/168755200)*ClassicalSixthBranch.v ((591052927:ℝ)/168755200)/ClassicalSixthBranch.r = (147907857747345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_592
  · change upperPayment 593 ≤ upperValue ((point split endpoint 4096 593+point split endpoint 4096 594)/2)
    have hp : upperPayment 593 = (388749090440:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 593+point split endpoint 4096 594)/2 = (591078077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591078077:ℝ)/168755200)*ClassicalSixthBranch.v ((591078077:ℝ)/168755200)/ClassicalSixthBranch.r = (147883040705177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_593
  · change upperPayment 594 ≤ upperValue ((point split endpoint 4096 594+point split endpoint 4096 595)/2)
    have hp : upperPayment 594 = (388683180845:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 594+point split endpoint 4096 595)/2 = (591103227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591103227:ℝ)/168755200)*ClassicalSixthBranch.v ((591103227:ℝ)/168755200)/ClassicalSixthBranch.r = (147858225687081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_594
  · change upperPayment 595 ≤ upperValue ((point split endpoint 4096 595+point split endpoint 4096 596)/2)
    have hp : upperPayment 595 = (388617250540:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 595+point split endpoint 4096 596)/2 = (591128377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591128377:ℝ)/168755200)*ClassicalSixthBranch.v ((591128377:ℝ)/168755200)/ClassicalSixthBranch.r = (147833412693057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_595
  · change upperPayment 596 ≤ upperValue ((point split endpoint 4096 596+point split endpoint 4096 597)/2)
    have hp : upperPayment 596 = (388551299522:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 596+point split endpoint 4096 597)/2 = (591153527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591153527:ℝ)/168755200)*ClassicalSixthBranch.v ((591153527:ℝ)/168755200)/ClassicalSixthBranch.r = (147808601723105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_596
  · change upperPayment 597 ≤ upperValue ((point split endpoint 4096 597+point split endpoint 4096 598)/2)
    have hp : upperPayment 597 = (388485327789:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 597+point split endpoint 4096 598)/2 = (591178677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591178677:ℝ)/168755200)*ClassicalSixthBranch.v ((591178677:ℝ)/168755200)/ClassicalSixthBranch.r = (147783792777225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_597
  · change upperPayment 598 ≤ upperValue ((point split endpoint 4096 598+point split endpoint 4096 599)/2)
    have hp : upperPayment 598 = (388419335337:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 598+point split endpoint 4096 599)/2 = (591203827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591203827:ℝ)/168755200)*ClassicalSixthBranch.v ((591203827:ℝ)/168755200)/ClassicalSixthBranch.r = (147758985855417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_598
  · change upperPayment 599 ≤ upperValue ((point split endpoint 4096 599+point split endpoint 4096 600)/2)
    have hp : upperPayment 599 = (388353322164:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 599+point split endpoint 4096 600)/2 = (591228977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591228977:ℝ)/168755200)*ClassicalSixthBranch.v ((591228977:ℝ)/168755200)/ClassicalSixthBranch.r = (147734180957681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_599
  · change upperPayment 600 ≤ upperValue ((point split endpoint 4096 600+point split endpoint 4096 601)/2)
    have hp : upperPayment 600 = (388287288267:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 600+point split endpoint 4096 601)/2 = (591254127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591254127:ℝ)/168755200)*ClassicalSixthBranch.v ((591254127:ℝ)/168755200)/ClassicalSixthBranch.r = (147709378084017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_600
  · change upperPayment 601 ≤ upperValue ((point split endpoint 4096 601+point split endpoint 4096 602)/2)
    have hp : upperPayment 601 = (388221233643:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 601+point split endpoint 4096 602)/2 = (591279277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591279277:ℝ)/168755200)*ClassicalSixthBranch.v ((591279277:ℝ)/168755200)/ClassicalSixthBranch.r = (147684577234425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_601
  · change upperPayment 602 ≤ upperValue ((point split endpoint 4096 602+point split endpoint 4096 603)/2)
    have hp : upperPayment 602 = (388155158289:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 602+point split endpoint 4096 603)/2 = (591304427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591304427:ℝ)/168755200)*ClassicalSixthBranch.v ((591304427:ℝ)/168755200)/ClassicalSixthBranch.r = (147659778408905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_602
  · change upperPayment 603 ≤ upperValue ((point split endpoint 4096 603+point split endpoint 4096 604)/2)
    have hp : upperPayment 603 = (388089062202:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 603+point split endpoint 4096 604)/2 = (591329577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591329577:ℝ)/168755200)*ClassicalSixthBranch.v ((591329577:ℝ)/168755200)/ClassicalSixthBranch.r = (147634981607457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_603
  · change upperPayment 604 ≤ upperValue ((point split endpoint 4096 604+point split endpoint 4096 605)/2)
    have hp : upperPayment 604 = (388022945380:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 604+point split endpoint 4096 605)/2 = (591354727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591354727:ℝ)/168755200)*ClassicalSixthBranch.v ((591354727:ℝ)/168755200)/ClassicalSixthBranch.r = (147610186830081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_604
  · change upperPayment 605 ≤ upperValue ((point split endpoint 4096 605+point split endpoint 4096 606)/2)
    have hp : upperPayment 605 = (387956807819:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 605+point split endpoint 4096 606)/2 = (591379877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591379877:ℝ)/168755200)*ClassicalSixthBranch.v ((591379877:ℝ)/168755200)/ClassicalSixthBranch.r = (147585394076777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_605
  · change upperPayment 606 ≤ upperValue ((point split endpoint 4096 606+point split endpoint 4096 607)/2)
    have hp : upperPayment 606 = (387890649517:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 606+point split endpoint 4096 607)/2 = (591405027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591405027:ℝ)/168755200)*ClassicalSixthBranch.v ((591405027:ℝ)/168755200)/ClassicalSixthBranch.r = (147560603347545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_606
  · change upperPayment 607 ≤ upperValue ((point split endpoint 4096 607+point split endpoint 4096 608)/2)
    have hp : upperPayment 607 = (387824470472:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 607+point split endpoint 4096 608)/2 = (591430177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591430177:ℝ)/168755200)*ClassicalSixthBranch.v ((591430177:ℝ)/168755200)/ClassicalSixthBranch.r = (147535814642385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_607
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_037
