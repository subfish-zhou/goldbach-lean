import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints041
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_041 (j : Fin 16) : upperPayment (16*41+j.val) ≤
    upperValue ((point split endpoint 4096 (16*41+j.val)+point split endpoint 4096 (16*41+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 656 ≤ upperValue ((point split endpoint 4096 656+point split endpoint 4096 657)/2)
    have hp : upperPayment 656 = (384556225889:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 656+point split endpoint 4096 657)/2 = (592662527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592662527:ℝ)/168755200)*ClassicalSixthBranch.v ((592662527:ℝ)/168755200)/ClassicalSixthBranch.r = (146323647577745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_656
  · change upperPayment 657 ≤ upperValue ((point split endpoint 4096 657+point split endpoint 4096 658)/2)
    have hp : upperPayment 657 = (384489005969:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 657+point split endpoint 4096 658)/2 = (592687677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592687677:ℝ)/168755200)*ClassicalSixthBranch.v ((592687677:ℝ)/168755200)/ClassicalSixthBranch.r = (146298960076185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_657
  · change upperPayment 658 ≤ upperValue ((point split endpoint 4096 658+point split endpoint 4096 659)/2)
    have hp : upperPayment 658 = (384421765157:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 658+point split endpoint 4096 659)/2 = (592712827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592712827:ℝ)/168755200)*ClassicalSixthBranch.v ((592712827:ℝ)/168755200)/ClassicalSixthBranch.r = (146274274598697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_658
  · change upperPayment 659 ≤ upperValue ((point split endpoint 4096 659+point split endpoint 4096 660)/2)
    have hp : upperPayment 659 = (384354503451:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 659+point split endpoint 4096 660)/2 = (592737977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592737977:ℝ)/168755200)*ClassicalSixthBranch.v ((592737977:ℝ)/168755200)/ClassicalSixthBranch.r = (146249591145281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_659
  · change upperPayment 660 ≤ upperValue ((point split endpoint 4096 660+point split endpoint 4096 661)/2)
    have hp : upperPayment 660 = (384287220847:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 660+point split endpoint 4096 661)/2 = (592763127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592763127:ℝ)/168755200)*ClassicalSixthBranch.v ((592763127:ℝ)/168755200)/ClassicalSixthBranch.r = (146224909715937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_660
  · change upperPayment 661 ≤ upperValue ((point split endpoint 4096 661+point split endpoint 4096 662)/2)
    have hp : upperPayment 661 = (384219917344:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 661+point split endpoint 4096 662)/2 = (592788277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592788277:ℝ)/168755200)*ClassicalSixthBranch.v ((592788277:ℝ)/168755200)/ClassicalSixthBranch.r = (146200230310665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_661
  · change upperPayment 662 ≤ upperValue ((point split endpoint 4096 662+point split endpoint 4096 663)/2)
    have hp : upperPayment 662 = (384152592937:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 662+point split endpoint 4096 663)/2 = (592813427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592813427:ℝ)/168755200)*ClassicalSixthBranch.v ((592813427:ℝ)/168755200)/ClassicalSixthBranch.r = (146175552929465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_662
  · change upperPayment 663 ≤ upperValue ((point split endpoint 4096 663+point split endpoint 4096 664)/2)
    have hp : upperPayment 663 = (384085247624:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 663+point split endpoint 4096 664)/2 = (592838577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592838577:ℝ)/168755200)*ClassicalSixthBranch.v ((592838577:ℝ)/168755200)/ClassicalSixthBranch.r = (110136305631:ℝ)/55297703936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_663
  · change upperPayment 664 ≤ upperValue ((point split endpoint 4096 664+point split endpoint 4096 665)/2)
    have hp : upperPayment 664 = (384017881402:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 664+point split endpoint 4096 665)/2 = (592863727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592863727:ℝ)/168755200)*ClassicalSixthBranch.v ((592863727:ℝ)/168755200)/ClassicalSixthBranch.r = (146126204239281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_664
  · change upperPayment 665 ≤ upperValue ((point split endpoint 4096 665+point split endpoint 4096 666)/2)
    have hp : upperPayment 665 = (383950494268:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 665+point split endpoint 4096 666)/2 = (592888877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592888877:ℝ)/168755200)*ClassicalSixthBranch.v ((592888877:ℝ)/168755200)/ClassicalSixthBranch.r = (146101532930297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_665
  · change upperPayment 666 ≤ upperValue ((point split endpoint 4096 666+point split endpoint 4096 667)/2)
    have hp : upperPayment 666 = (383883086219:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 666+point split endpoint 4096 667)/2 = (592914027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592914027:ℝ)/168755200)*ClassicalSixthBranch.v ((592914027:ℝ)/168755200)/ClassicalSixthBranch.r = (146076863645385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_666
  · change upperPayment 667 ≤ upperValue ((point split endpoint 4096 667+point split endpoint 4096 668)/2)
    have hp : upperPayment 667 = (383815657252:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 667+point split endpoint 4096 668)/2 = (592939177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592939177:ℝ)/168755200)*ClassicalSixthBranch.v ((592939177:ℝ)/168755200)/ClassicalSixthBranch.r = (146052196384545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_667
  · change upperPayment 668 ≤ upperValue ((point split endpoint 4096 668+point split endpoint 4096 669)/2)
    have hp : upperPayment 668 = (383748207364:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 668+point split endpoint 4096 669)/2 = (592964327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592964327:ℝ)/168755200)*ClassicalSixthBranch.v ((592964327:ℝ)/168755200)/ClassicalSixthBranch.r = (146027531147777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_668
  · change upperPayment 669 ≤ upperValue ((point split endpoint 4096 669+point split endpoint 4096 670)/2)
    have hp : upperPayment 669 = (383680736553:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 669+point split endpoint 4096 670)/2 = (592989477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592989477:ℝ)/168755200)*ClassicalSixthBranch.v ((592989477:ℝ)/168755200)/ClassicalSixthBranch.r = (146002867935081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_669
  · change upperPayment 670 ≤ upperValue ((point split endpoint 4096 670+point split endpoint 4096 671)/2)
    have hp : upperPayment 670 = (383613244815:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 670+point split endpoint 4096 671)/2 = (593014627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593014627:ℝ)/168755200)*ClassicalSixthBranch.v ((593014627:ℝ)/168755200)/ClassicalSixthBranch.r = (145978206746457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_670
  · change upperPayment 671 ≤ upperValue ((point split endpoint 4096 671+point split endpoint 4096 672)/2)
    have hp : upperPayment 671 = (383545732148:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 671+point split endpoint 4096 672)/2 = (593039777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((593039777:ℝ)/168755200)*ClassicalSixthBranch.v ((593039777:ℝ)/168755200)/ClassicalSixthBranch.r = (145953547581905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_671
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_041
