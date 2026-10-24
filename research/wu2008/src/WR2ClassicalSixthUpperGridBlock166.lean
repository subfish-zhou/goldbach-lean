import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints166
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_166 (j : Fin 16) : upperPayment (16*166+j.val) ≤
    upperValue ((point split endpoint 4096 (16*166+j.val)+point split endpoint 4096 (16*166+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2656 ≤ upperValue ((point split endpoint 4096 2656+point split endpoint 4096 2657)/2)
    have hp : upperPayment 2656 = (203441064275:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2656+point split endpoint 4096 2657)/2 = (642962527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642962527:ℝ)/168755200)*ClassicalSixthBranch.v ((642962527:ℝ)/168755200)/ClassicalSixthBranch.r = (100994764385745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2656
  · change upperPayment 2657 ≤ upperValue ((point split endpoint 4096 2657+point split endpoint 4096 2658)/2)
    have hp : upperPayment 2657 = (203324100411:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2657+point split endpoint 4096 2658)/2 = (642987677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642987677:ℝ)/168755200)*ClassicalSixthBranch.v ((642987677:ℝ)/168755200)/ClassicalSixthBranch.r = (100974125028185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2657
  · change upperPayment 2658 ≤ upperValue ((point split endpoint 4096 2658+point split endpoint 4096 2659)/2)
    have hp : upperPayment 2658 = (203207106434:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2658+point split endpoint 4096 2659)/2 = (643012827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643012827:ℝ)/168755200)*ClassicalSixthBranch.v ((643012827:ℝ)/168755200)/ClassicalSixthBranch.r = (100953487694697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2658
  · change upperPayment 2659 ≤ upperValue ((point split endpoint 4096 2659+point split endpoint 4096 2660)/2)
    have hp : upperPayment 2659 = (203090082338:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2659+point split endpoint 4096 2660)/2 = (643037977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643037977:ℝ)/168755200)*ClassicalSixthBranch.v ((643037977:ℝ)/168755200)/ClassicalSixthBranch.r = (100932852385281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2659
  · change upperPayment 2660 ≤ upperValue ((point split endpoint 4096 2660+point split endpoint 4096 2661)/2)
    have hp : upperPayment 2660 = (202973028117:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2660+point split endpoint 4096 2661)/2 = (643063127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643063127:ℝ)/168755200)*ClassicalSixthBranch.v ((643063127:ℝ)/168755200)/ClassicalSixthBranch.r = (100912219099937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2660
  · change upperPayment 2661 ≤ upperValue ((point split endpoint 4096 2661+point split endpoint 4096 2662)/2)
    have hp : upperPayment 2661 = (202855943763:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2661+point split endpoint 4096 2662)/2 = (643088277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643088277:ℝ)/168755200)*ClassicalSixthBranch.v ((643088277:ℝ)/168755200)/ClassicalSixthBranch.r = (100891587838665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2661
  · change upperPayment 2662 ≤ upperValue ((point split endpoint 4096 2662+point split endpoint 4096 2663)/2)
    have hp : upperPayment 2662 = (202738829270:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2662+point split endpoint 4096 2663)/2 = (643113427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643113427:ℝ)/168755200)*ClassicalSixthBranch.v ((643113427:ℝ)/168755200)/ClassicalSixthBranch.r = (100870958601465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2662
  · change upperPayment 2663 ≤ upperValue ((point split endpoint 4096 2663+point split endpoint 4096 2664)/2)
    have hp : upperPayment 2663 = (202621684630:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2663+point split endpoint 4096 2664)/2 = (643138577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643138577:ℝ)/168755200)*ClassicalSixthBranch.v ((643138577:ℝ)/168755200)/ClassicalSixthBranch.r = (100850331388337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2663
  · change upperPayment 2664 ≤ upperValue ((point split endpoint 4096 2664+point split endpoint 4096 2665)/2)
    have hp : upperPayment 2664 = (202504509838:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2664+point split endpoint 4096 2665)/2 = (643163727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643163727:ℝ)/168755200)*ClassicalSixthBranch.v ((643163727:ℝ)/168755200)/ClassicalSixthBranch.r = (100829706199281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2664
  · change upperPayment 2665 ≤ upperValue ((point split endpoint 4096 2665+point split endpoint 4096 2666)/2)
    have hp : upperPayment 2665 = (202387304887:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2665+point split endpoint 4096 2666)/2 = (643188877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643188877:ℝ)/168755200)*ClassicalSixthBranch.v ((643188877:ℝ)/168755200)/ClassicalSixthBranch.r = (100809083034297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2665
  · change upperPayment 2666 ≤ upperValue ((point split endpoint 4096 2666+point split endpoint 4096 2667)/2)
    have hp : upperPayment 2666 = (202270069769:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2666+point split endpoint 4096 2667)/2 = (643214027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643214027:ℝ)/168755200)*ClassicalSixthBranch.v ((643214027:ℝ)/168755200)/ClassicalSixthBranch.r = (100788461893385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2666
  · change upperPayment 2667 ≤ upperValue ((point split endpoint 4096 2667+point split endpoint 4096 2668)/2)
    have hp : upperPayment 2667 = (202152804479:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2667+point split endpoint 4096 2668)/2 = (643239177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643239177:ℝ)/168755200)*ClassicalSixthBranch.v ((643239177:ℝ)/168755200)/ClassicalSixthBranch.r = (100767842776545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2667
  · change upperPayment 2668 ≤ upperValue ((point split endpoint 4096 2668+point split endpoint 4096 2669)/2)
    have hp : upperPayment 2668 = (202035509008:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2668+point split endpoint 4096 2669)/2 = (643264327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643264327:ℝ)/168755200)*ClassicalSixthBranch.v ((643264327:ℝ)/168755200)/ClassicalSixthBranch.r = (100747225683777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2668
  · change upperPayment 2669 ≤ upperValue ((point split endpoint 4096 2669+point split endpoint 4096 2670)/2)
    have hp : upperPayment 2669 = (201918183351:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2669+point split endpoint 4096 2670)/2 = (643289477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643289477:ℝ)/168755200)*ClassicalSixthBranch.v ((643289477:ℝ)/168755200)/ClassicalSixthBranch.r = (100726610615081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2669
  · change upperPayment 2670 ≤ upperValue ((point split endpoint 4096 2670+point split endpoint 4096 2671)/2)
    have hp : upperPayment 2670 = (201800827501:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2670+point split endpoint 4096 2671)/2 = (643314627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643314627:ℝ)/168755200)*ClassicalSixthBranch.v ((643314627:ℝ)/168755200)/ClassicalSixthBranch.r = (100705997570457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2670
  · change upperPayment 2671 ≤ upperValue ((point split endpoint 4096 2671+point split endpoint 4096 2672)/2)
    have hp : upperPayment 2671 = (201683441450:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2671+point split endpoint 4096 2672)/2 = (643339777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((643339777:ℝ)/168755200)*ClassicalSixthBranch.v ((643339777:ℝ)/168755200)/ClassicalSixthBranch.r = (100685386549905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2671
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_166
