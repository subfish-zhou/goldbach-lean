import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints035
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_035 (j : Fin 16) : upperPayment (16*35+j.val) ≤
    upperValue ((point split endpoint 4096 (16*35+j.val)+point split endpoint 4096 (16*35+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 560 ≤ upperValue ((point split endpoint 4096 560+point split endpoint 4096 561)/2)
    have hp : upperPayment 560 = (390912507316:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 560+point split endpoint 4096 561)/2 = (590248127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590248127:ℝ)/168755200)*ClassicalSixthBranch.v ((590248127:ℝ)/168755200)/ClassicalSixthBranch.r = (148703071806737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_560
  · change upperPayment 561 ≤ upperValue ((point split endpoint 4096 561+point split endpoint 4096 562)/2)
    have hp : upperPayment 561 = (390847279564:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 561+point split endpoint 4096 562)/2 = (590273277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590273277:ℝ)/168755200)*ClassicalSixthBranch.v ((590273277:ℝ)/168755200)/ClassicalSixthBranch.r = (148678189994265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_561
  · change upperPayment 562 ≤ upperValue ((point split endpoint 4096 562+point split endpoint 4096 563)/2)
    have hp : upperPayment 562 = (390782031195:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 562+point split endpoint 4096 563)/2 = (590298427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590298427:ℝ)/168755200)*ClassicalSixthBranch.v ((590298427:ℝ)/168755200)/ClassicalSixthBranch.r = (148653310205865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_562
  · change upperPayment 563 ≤ upperValue ((point split endpoint 4096 563+point split endpoint 4096 564)/2)
    have hp : upperPayment 563 = (390716762206:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 563+point split endpoint 4096 564)/2 = (590323577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590323577:ℝ)/168755200)*ClassicalSixthBranch.v ((590323577:ℝ)/168755200)/ClassicalSixthBranch.r = (148628432441537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_563
  · change upperPayment 564 ≤ upperValue ((point split endpoint 4096 564+point split endpoint 4096 565)/2)
    have hp : upperPayment 564 = (390651472595:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 564+point split endpoint 4096 565)/2 = (590348727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590348727:ℝ)/168755200)*ClassicalSixthBranch.v ((590348727:ℝ)/168755200)/ClassicalSixthBranch.r = (148603556701281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_564
  · change upperPayment 565 ≤ upperValue ((point split endpoint 4096 565+point split endpoint 4096 566)/2)
    have hp : upperPayment 565 = (390586162358:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 565+point split endpoint 4096 566)/2 = (590373877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590373877:ℝ)/168755200)*ClassicalSixthBranch.v ((590373877:ℝ)/168755200)/ClassicalSixthBranch.r = (148578682985097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_565
  · change upperPayment 566 ≤ upperValue ((point split endpoint 4096 566+point split endpoint 4096 567)/2)
    have hp : upperPayment 566 = (390520831493:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 566+point split endpoint 4096 567)/2 = (590399027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590399027:ℝ)/168755200)*ClassicalSixthBranch.v ((590399027:ℝ)/168755200)/ClassicalSixthBranch.r = (148553811292985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_566
  · change upperPayment 567 ≤ upperValue ((point split endpoint 4096 567+point split endpoint 4096 568)/2)
    have hp : upperPayment 567 = (390455479998:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 567+point split endpoint 4096 568)/2 = (590424177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590424177:ℝ)/168755200)*ClassicalSixthBranch.v ((590424177:ℝ)/168755200)/ClassicalSixthBranch.r = (148528941624945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_567
  · change upperPayment 568 ≤ upperValue ((point split endpoint 4096 568+point split endpoint 4096 569)/2)
    have hp : upperPayment 568 = (390390107868:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 568+point split endpoint 4096 569)/2 = (590449327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590449327:ℝ)/168755200)*ClassicalSixthBranch.v ((590449327:ℝ)/168755200)/ClassicalSixthBranch.r = (148504073980977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_568
  · change upperPayment 569 ≤ upperValue ((point split endpoint 4096 569+point split endpoint 4096 570)/2)
    have hp : upperPayment 569 = (390324715102:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 569+point split endpoint 4096 570)/2 = (590474477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590474477:ℝ)/168755200)*ClassicalSixthBranch.v ((590474477:ℝ)/168755200)/ClassicalSixthBranch.r = (148479208361081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_569
  · change upperPayment 570 ≤ upperValue ((point split endpoint 4096 570+point split endpoint 4096 571)/2)
    have hp : upperPayment 570 = (390259301697:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 570+point split endpoint 4096 571)/2 = (590499627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590499627:ℝ)/168755200)*ClassicalSixthBranch.v ((590499627:ℝ)/168755200)/ClassicalSixthBranch.r = (148454344765257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_570
  · change upperPayment 571 ≤ upperValue ((point split endpoint 4096 571+point split endpoint 4096 572)/2)
    have hp : upperPayment 571 = (390193867649:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 571+point split endpoint 4096 572)/2 = (590524777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590524777:ℝ)/168755200)*ClassicalSixthBranch.v ((590524777:ℝ)/168755200)/ClassicalSixthBranch.r = (148429483193505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_571
  · change upperPayment 572 ≤ upperValue ((point split endpoint 4096 572+point split endpoint 4096 573)/2)
    have hp : upperPayment 572 = (390128412957:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 572+point split endpoint 4096 573)/2 = (590549927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590549927:ℝ)/168755200)*ClassicalSixthBranch.v ((590549927:ℝ)/168755200)/ClassicalSixthBranch.r = (148404623645825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_572
  · change upperPayment 573 ≤ upperValue ((point split endpoint 4096 573+point split endpoint 4096 574)/2)
    have hp : upperPayment 573 = (390062937617:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 573+point split endpoint 4096 574)/2 = (590575077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590575077:ℝ)/168755200)*ClassicalSixthBranch.v ((590575077:ℝ)/168755200)/ClassicalSixthBranch.r = (148379766122217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_573
  · change upperPayment 574 ≤ upperValue ((point split endpoint 4096 574+point split endpoint 4096 575)/2)
    have hp : upperPayment 574 = (389997441626:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 574+point split endpoint 4096 575)/2 = (590600227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590600227:ℝ)/168755200)*ClassicalSixthBranch.v ((590600227:ℝ)/168755200)/ClassicalSixthBranch.r = (148354910622681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_574
  · change upperPayment 575 ≤ upperValue ((point split endpoint 4096 575+point split endpoint 4096 576)/2)
    have hp : upperPayment 575 = (389931924982:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 575+point split endpoint 4096 576)/2 = (590625377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((590625377:ℝ)/168755200)*ClassicalSixthBranch.v ((590625377:ℝ)/168755200)/ClassicalSixthBranch.r = (148330057147217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_575
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_035
