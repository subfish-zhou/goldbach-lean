import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints165
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_165 (j : Fin 16) : upperPayment (16*165+j.val) ≤
    upperValue ((point split endpoint 4096 (16*165+j.val)+point split endpoint 4096 (16*165+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2640 ≤ upperValue ((point split endpoint 4096 2640+point split endpoint 4096 2641)/2)
    have hp : upperPayment 2640 = (205308396329:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2640+point split endpoint 4096 2641)/2 = (642560127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642560127:ℝ)/168755200)*ClassicalSixthBranch.v ((642560127:ℝ)/168755200)/ClassicalSixthBranch.r = (101325269380497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2640
  · change upperPayment 2641 ≤ upperValue ((point split endpoint 4096 2641+point split endpoint 4096 2642)/2)
    have hp : upperPayment 2641 = (205191913346:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2641+point split endpoint 4096 2642)/2 = (642585277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642585277:ℝ)/168755200)*ClassicalSixthBranch.v ((642585277:ℝ)/168755200)/ClassicalSixthBranch.r = (101304597637785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2641
  · change upperPayment 2642 ≤ upperValue ((point split endpoint 4096 2642+point split endpoint 4096 2643)/2)
    have hp : upperPayment 2642 = (205075400359:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2642+point split endpoint 4096 2643)/2 = (642610427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642610427:ℝ)/168755200)*ClassicalSixthBranch.v ((642610427:ℝ)/168755200)/ClassicalSixthBranch.r = (101283927919145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2642
  · change upperPayment 2643 ≤ upperValue ((point split endpoint 4096 2643+point split endpoint 4096 2644)/2)
    have hp : upperPayment 2643 = (204958857360:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2643+point split endpoint 4096 2644)/2 = (642635577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642635577:ℝ)/168755200)*ClassicalSixthBranch.v ((642635577:ℝ)/168755200)/ClassicalSixthBranch.r = (101263260224577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2643
  · change upperPayment 2644 ≤ upperValue ((point split endpoint 4096 2644+point split endpoint 4096 2645)/2)
    have hp : upperPayment 2644 = (204842284343:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2644+point split endpoint 4096 2645)/2 = (642660727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642660727:ℝ)/168755200)*ClassicalSixthBranch.v ((642660727:ℝ)/168755200)/ClassicalSixthBranch.r = (101242594554081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2644
  · change upperPayment 2645 ≤ upperValue ((point split endpoint 4096 2645+point split endpoint 4096 2646)/2)
    have hp : upperPayment 2645 = (204725681300:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2645+point split endpoint 4096 2646)/2 = (642685877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642685877:ℝ)/168755200)*ClassicalSixthBranch.v ((642685877:ℝ)/168755200)/ClassicalSixthBranch.r = (101221930907657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2645
  · change upperPayment 2646 ≤ upperValue ((point split endpoint 4096 2646+point split endpoint 4096 2647)/2)
    have hp : upperPayment 2646 = (204609048227:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2646+point split endpoint 4096 2647)/2 = (642711027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642711027:ℝ)/168755200)*ClassicalSixthBranch.v ((642711027:ℝ)/168755200)/ClassicalSixthBranch.r = (101201269285305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2646
  · change upperPayment 2647 ≤ upperValue ((point split endpoint 4096 2647+point split endpoint 4096 2648)/2)
    have hp : upperPayment 2647 = (204492385115:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2647+point split endpoint 4096 2648)/2 = (642736177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642736177:ℝ)/168755200)*ClassicalSixthBranch.v ((642736177:ℝ)/168755200)/ClassicalSixthBranch.r = (101180609687025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2647
  · change upperPayment 2648 ≤ upperValue ((point split endpoint 4096 2648+point split endpoint 4096 2649)/2)
    have hp : upperPayment 2648 = (204375691958:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2648+point split endpoint 4096 2649)/2 = (642761327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642761327:ℝ)/168755200)*ClassicalSixthBranch.v ((642761327:ℝ)/168755200)/ClassicalSixthBranch.r = (101159952112817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2648
  · change upperPayment 2649 ≤ upperValue ((point split endpoint 4096 2649+point split endpoint 4096 2650)/2)
    have hp : upperPayment 2649 = (204258968749:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2649+point split endpoint 4096 2650)/2 = (642786477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642786477:ℝ)/168755200)*ClassicalSixthBranch.v ((642786477:ℝ)/168755200)/ClassicalSixthBranch.r = (101139296562681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2649
  · change upperPayment 2650 ≤ upperValue ((point split endpoint 4096 2650+point split endpoint 4096 2651)/2)
    have hp : upperPayment 2650 = (204142215482:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2650+point split endpoint 4096 2651)/2 = (642811627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642811627:ℝ)/168755200)*ClassicalSixthBranch.v ((642811627:ℝ)/168755200)/ClassicalSixthBranch.r = (101118643036617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2650
  · change upperPayment 2651 ≤ upperValue ((point split endpoint 4096 2651+point split endpoint 4096 2652)/2)
    have hp : upperPayment 2651 = (204025432149:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2651+point split endpoint 4096 2652)/2 = (642836777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642836777:ℝ)/168755200)*ClassicalSixthBranch.v ((642836777:ℝ)/168755200)/ClassicalSixthBranch.r = (101097991534625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2651
  · change upperPayment 2652 ≤ upperValue ((point split endpoint 4096 2652+point split endpoint 4096 2653)/2)
    have hp : upperPayment 2652 = (203908618745:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2652+point split endpoint 4096 2653)/2 = (642861927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642861927:ℝ)/168755200)*ClassicalSixthBranch.v ((642861927:ℝ)/168755200)/ClassicalSixthBranch.r = (101077342056705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2652
  · change upperPayment 2653 ≤ upperValue ((point split endpoint 4096 2653+point split endpoint 4096 2654)/2)
    have hp : upperPayment 2653 = (203791775262:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2653+point split endpoint 4096 2654)/2 = (642887077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642887077:ℝ)/168755200)*ClassicalSixthBranch.v ((642887077:ℝ)/168755200)/ClassicalSixthBranch.r = (101056694602857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2653
  · change upperPayment 2654 ≤ upperValue ((point split endpoint 4096 2654+point split endpoint 4096 2655)/2)
    have hp : upperPayment 2654 = (203674901694:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2654+point split endpoint 4096 2655)/2 = (642912227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642912227:ℝ)/168755200)*ClassicalSixthBranch.v ((642912227:ℝ)/168755200)/ClassicalSixthBranch.r = (101036049173081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2654
  · change upperPayment 2655 ≤ upperValue ((point split endpoint 4096 2655+point split endpoint 4096 2656)/2)
    have hp : upperPayment 2655 = (203557998034:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2655+point split endpoint 4096 2656)/2 = (642937377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642937377:ℝ)/168755200)*ClassicalSixthBranch.v ((642937377:ℝ)/168755200)/ClassicalSixthBranch.r = (101015405767377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2655
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_165
