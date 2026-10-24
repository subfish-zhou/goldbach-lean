import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints163
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_163 (j : Fin 16) : upperPayment (16*163+j.val) ≤
    upperValue ((point split endpoint 4096 (16*163+j.val)+point split endpoint 4096 (16*163+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2608 ≤ upperValue ((point split endpoint 4096 2608+point split endpoint 4096 2609)/2)
    have hp : upperPayment 2608 = (209020049188:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2608+point split endpoint 4096 2609)/2 = (641755327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641755327:ℝ)/168755200)*ClassicalSixthBranch.v ((641755327:ℝ)/168755200)/ClassicalSixthBranch.r = (101987833857297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2608
  · change upperPayment 2609 ≤ upperValue ((point split endpoint 4096 2609+point split endpoint 4096 2610)/2)
    have hp : upperPayment 2609 = (208904522838:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2609+point split endpoint 4096 2610)/2 = (641780477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641780477:ℝ)/168755200)*ClassicalSixthBranch.v ((641780477:ℝ)/168755200)/ClassicalSixthBranch.r = (101967097344281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2609
  · change upperPayment 2610 ≤ upperValue ((point split endpoint 4096 2610+point split endpoint 4096 2611)/2)
    have hp : upperPayment 2610 = (208788966697:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2610+point split endpoint 4096 2611)/2 = (641805627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641805627:ℝ)/168755200)*ClassicalSixthBranch.v ((641805627:ℝ)/168755200)/ClassicalSixthBranch.r = (101946362855337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2610
  · change upperPayment 2611 ≤ upperValue ((point split endpoint 4096 2611+point split endpoint 4096 2612)/2)
    have hp : upperPayment 2611 = (208673380757:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2611+point split endpoint 4096 2612)/2 = (641830777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641830777:ℝ)/168755200)*ClassicalSixthBranch.v ((641830777:ℝ)/168755200)/ClassicalSixthBranch.r = (101925630390465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2611
  · change upperPayment 2612 ≤ upperValue ((point split endpoint 4096 2612+point split endpoint 4096 2613)/2)
    have hp : upperPayment 2612 = (208557765011:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2612+point split endpoint 4096 2613)/2 = (641855927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641855927:ℝ)/168755200)*ClassicalSixthBranch.v ((641855927:ℝ)/168755200)/ClassicalSixthBranch.r = (101904899949665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2612
  · change upperPayment 2613 ≤ upperValue ((point split endpoint 4096 2613+point split endpoint 4096 2614)/2)
    have hp : upperPayment 2613 = (208442119454:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2613+point split endpoint 4096 2614)/2 = (641881077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641881077:ℝ)/168755200)*ClassicalSixthBranch.v ((641881077:ℝ)/168755200)/ClassicalSixthBranch.r = (101884171532937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2613
  · change upperPayment 2614 ≤ upperValue ((point split endpoint 4096 2614+point split endpoint 4096 2615)/2)
    have hp : upperPayment 2614 = (208326444079:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2614+point split endpoint 4096 2615)/2 = (641906227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641906227:ℝ)/168755200)*ClassicalSixthBranch.v ((641906227:ℝ)/168755200)/ClassicalSixthBranch.r = (101863445140281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2614
  · change upperPayment 2615 ≤ upperValue ((point split endpoint 4096 2615+point split endpoint 4096 2616)/2)
    have hp : upperPayment 2615 = (208210738879:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2615+point split endpoint 4096 2616)/2 = (641931377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641931377:ℝ)/168755200)*ClassicalSixthBranch.v ((641931377:ℝ)/168755200)/ClassicalSixthBranch.r = (101842720771697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2615
  · change upperPayment 2616 ≤ upperValue ((point split endpoint 4096 2616+point split endpoint 4096 2617)/2)
    have hp : upperPayment 2616 = (208095003847:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2616+point split endpoint 4096 2617)/2 = (641956527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641956527:ℝ)/168755200)*ClassicalSixthBranch.v ((641956527:ℝ)/168755200)/ClassicalSixthBranch.r = (101821998427185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2616
  · change upperPayment 2617 ≤ upperValue ((point split endpoint 4096 2617+point split endpoint 4096 2618)/2)
    have hp : upperPayment 2617 = (207979238977:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2617+point split endpoint 4096 2618)/2 = (641981677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((641981677:ℝ)/168755200)*ClassicalSixthBranch.v ((641981677:ℝ)/168755200)/ClassicalSixthBranch.r = (101801278106745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2617
  · change upperPayment 2618 ≤ upperValue ((point split endpoint 4096 2618+point split endpoint 4096 2619)/2)
    have hp : upperPayment 2618 = (207863444262:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2618+point split endpoint 4096 2619)/2 = (642006827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642006827:ℝ)/168755200)*ClassicalSixthBranch.v ((642006827:ℝ)/168755200)/ClassicalSixthBranch.r = (101780559810377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2618
  · change upperPayment 2619 ≤ upperValue ((point split endpoint 4096 2619+point split endpoint 4096 2620)/2)
    have hp : upperPayment 2619 = (207747619695:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2619+point split endpoint 4096 2620)/2 = (642031977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642031977:ℝ)/168755200)*ClassicalSixthBranch.v ((642031977:ℝ)/168755200)/ClassicalSixthBranch.r = (101759843538081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2619
  · change upperPayment 2620 ≤ upperValue ((point split endpoint 4096 2620+point split endpoint 4096 2621)/2)
    have hp : upperPayment 2620 = (207631765270:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2620+point split endpoint 4096 2621)/2 = (642057127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642057127:ℝ)/168755200)*ClassicalSixthBranch.v ((642057127:ℝ)/168755200)/ClassicalSixthBranch.r = (101739129289857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2620
  · change upperPayment 2621 ≤ upperValue ((point split endpoint 4096 2621+point split endpoint 4096 2622)/2)
    have hp : upperPayment 2621 = (207515880981:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2621+point split endpoint 4096 2622)/2 = (642082277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642082277:ℝ)/168755200)*ClassicalSixthBranch.v ((642082277:ℝ)/168755200)/ClassicalSixthBranch.r = (101718417065705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2621
  · change upperPayment 2622 ≤ upperValue ((point split endpoint 4096 2622+point split endpoint 4096 2623)/2)
    have hp : upperPayment 2622 = (207399966820:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2622+point split endpoint 4096 2623)/2 = (642107427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642107427:ℝ)/168755200)*ClassicalSixthBranch.v ((642107427:ℝ)/168755200)/ClassicalSixthBranch.r = (101697706865625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2622
  · change upperPayment 2623 ≤ upperValue ((point split endpoint 4096 2623+point split endpoint 4096 2624)/2)
    have hp : upperPayment 2623 = (207284022781:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2623+point split endpoint 4096 2624)/2 = (642132577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((642132577:ℝ)/168755200)*ClassicalSixthBranch.v ((642132577:ℝ)/168755200)/ClassicalSixthBranch.r = (101676998689617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2623
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_163
