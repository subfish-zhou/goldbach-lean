import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints050
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_050 (j : Fin 16) : upperPayment (16*50+j.val) ≤
    upperValue ((point split endpoint 4096 (16*50+j.val)+point split endpoint 4096 (16*50+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 800 ≤ upperValue ((point split endpoint 4096 800+point split endpoint 4096 801)/2)
    have hp : upperPayment 800 = (374660009937:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 800+point split endpoint 4096 801)/2 = (596284127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596284127:ℝ)/168755200)*ClassicalSixthBranch.v ((596284127:ℝ)/168755200)/ClassicalSixthBranch.r = (142789487198417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_800
  · change upperPayment 801 ≤ upperValue ((point split endpoint 4096 801+point split endpoint 4096 802)/2)
    have hp : upperPayment 801 = (374589750865:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 801+point split endpoint 4096 802)/2 = (596309277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596309277:ℝ)/168755200)*ClassicalSixthBranch.v ((596309277:ℝ)/168755200)/ClassicalSixthBranch.r = (142765091163225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_801
  · change upperPayment 802 ≤ upperValue ((point split endpoint 4096 802+point split endpoint 4096 803)/2)
    have hp : upperPayment 802 = (374519470465:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 802+point split endpoint 4096 803)/2 = (596334427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596334427:ℝ)/168755200)*ClassicalSixthBranch.v ((596334427:ℝ)/168755200)/ClassicalSixthBranch.r = (142740697152105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_802
  · change upperPayment 803 ≤ upperValue ((point split endpoint 4096 803+point split endpoint 4096 804)/2)
    have hp : upperPayment 803 = (374449168736:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 803+point split endpoint 4096 804)/2 = (596359577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596359577:ℝ)/168755200)*ClassicalSixthBranch.v ((596359577:ℝ)/168755200)/ClassicalSixthBranch.r = (142716305165057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_803
  · change upperPayment 804 ≤ upperValue ((point split endpoint 4096 804+point split endpoint 4096 805)/2)
    have hp : upperPayment 804 = (374378845674:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 804+point split endpoint 4096 805)/2 = (596384727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596384727:ℝ)/168755200)*ClassicalSixthBranch.v ((596384727:ℝ)/168755200)/ClassicalSixthBranch.r = (142691915202081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_804
  · change upperPayment 805 ≤ upperValue ((point split endpoint 4096 805+point split endpoint 4096 806)/2)
    have hp : upperPayment 805 = (374308501275:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 805+point split endpoint 4096 806)/2 = (596409877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596409877:ℝ)/168755200)*ClassicalSixthBranch.v ((596409877:ℝ)/168755200)/ClassicalSixthBranch.r = (142667527263177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_805
  · change upperPayment 806 ≤ upperValue ((point split endpoint 4096 806+point split endpoint 4096 807)/2)
    have hp : upperPayment 806 = (374238135538:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 806+point split endpoint 4096 807)/2 = (596435027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596435027:ℝ)/168755200)*ClassicalSixthBranch.v ((596435027:ℝ)/168755200)/ClassicalSixthBranch.r = (142643141348345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_806
  · change upperPayment 807 ≤ upperValue ((point split endpoint 4096 807+point split endpoint 4096 808)/2)
    have hp : upperPayment 807 = (374167748457:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 807+point split endpoint 4096 808)/2 = (596460177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596460177:ℝ)/168755200)*ClassicalSixthBranch.v ((596460177:ℝ)/168755200)/ClassicalSixthBranch.r = (142618757457585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_807
  · change upperPayment 808 ≤ upperValue ((point split endpoint 4096 808+point split endpoint 4096 809)/2)
    have hp : upperPayment 808 = (374097340032:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 808+point split endpoint 4096 809)/2 = (596485327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596485327:ℝ)/168755200)*ClassicalSixthBranch.v ((596485327:ℝ)/168755200)/ClassicalSixthBranch.r = (142594375590897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_808
  · change upperPayment 809 ≤ upperValue ((point split endpoint 4096 809+point split endpoint 4096 810)/2)
    have hp : upperPayment 809 = (374026910257:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 809+point split endpoint 4096 810)/2 = (596510477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596510477:ℝ)/168755200)*ClassicalSixthBranch.v ((596510477:ℝ)/168755200)/ClassicalSixthBranch.r = (142569995748281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_809
  · change upperPayment 810 ≤ upperValue ((point split endpoint 4096 810+point split endpoint 4096 811)/2)
    have hp : upperPayment 810 = (373956459131:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 810+point split endpoint 4096 811)/2 = (596535627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596535627:ℝ)/168755200)*ClassicalSixthBranch.v ((596535627:ℝ)/168755200)/ClassicalSixthBranch.r = (142545617929737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_810
  · change upperPayment 811 ≤ upperValue ((point split endpoint 4096 811+point split endpoint 4096 812)/2)
    have hp : upperPayment 811 = (373885986650:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 811+point split endpoint 4096 812)/2 = (596560777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596560777:ℝ)/168755200)*ClassicalSixthBranch.v ((596560777:ℝ)/168755200)/ClassicalSixthBranch.r = (142521242135265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_811
  · change upperPayment 812 ≤ upperValue ((point split endpoint 4096 812+point split endpoint 4096 813)/2)
    have hp : upperPayment 812 = (373815492811:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 812+point split endpoint 4096 813)/2 = (596585927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596585927:ℝ)/168755200)*ClassicalSixthBranch.v ((596585927:ℝ)/168755200)/ClassicalSixthBranch.r = (142496868364865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_812
  · change upperPayment 813 ≤ upperValue ((point split endpoint 4096 813+point split endpoint 4096 814)/2)
    have hp : upperPayment 813 = (373744977611:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 813+point split endpoint 4096 814)/2 = (596611077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596611077:ℝ)/168755200)*ClassicalSixthBranch.v ((596611077:ℝ)/168755200)/ClassicalSixthBranch.r = (142472496618537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_813
  · change upperPayment 814 ≤ upperValue ((point split endpoint 4096 814+point split endpoint 4096 815)/2)
    have hp : upperPayment 814 = (373674441046:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 814+point split endpoint 4096 815)/2 = (596636227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596636227:ℝ)/168755200)*ClassicalSixthBranch.v ((596636227:ℝ)/168755200)/ClassicalSixthBranch.r = (142448126896281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_814
  · change upperPayment 815 ≤ upperValue ((point split endpoint 4096 815+point split endpoint 4096 816)/2)
    have hp : upperPayment 815 = (373603883114:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 815+point split endpoint 4096 816)/2 = (596661377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((596661377:ℝ)/168755200)*ClassicalSixthBranch.v ((596661377:ℝ)/168755200)/ClassicalSixthBranch.r = (142423759198097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_815
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_050
