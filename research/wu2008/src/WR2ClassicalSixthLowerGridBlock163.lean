import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints163
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_163 (j : Fin 16) : lowerPayment (16*163+j.val) ≤
    lowerValue ((point 2 split 4096 (16*163+j.val)+point 2 split 4096 (16*163+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2608 ≤ lowerValue ((point 2 split 4096 2608+point 2 split 4096 2609)/2)
    have hp : lowerPayment 2608 = (286799878510:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2608+point 2 split 4096 2609)/2 = (489486827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489486827:ℝ)/168755200)/ClassicalSixthBranch.v ((489486827:ℝ)/168755200) = (24493698323:ℝ)/11813995352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2608
  · change lowerPayment 2609 ≤ lowerValue ((point 2 split 4096 2609+point 2 split 4096 2610)/2)
    have hp : lowerPayment 2609 = (286887659143:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2609+point 2 split 4096 2610)/2 = (489545089:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489545089:ℝ)/168755200)/ClassicalSixthBranch.v ((489545089:ℝ)/168755200) = (612265144401:ℝ)/295301875912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2609
  · change lowerPayment 2610 ≤ lowerValue ((point 2 split 4096 2610+point 2 split 4096 2611)/2)
    have hp : lowerPayment 2610 = (286975438897:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2610+point 2 split 4096 2611)/2 = (489603351:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489603351:ℝ)/168755200)/ClassicalSixthBranch.v ((489603351:ℝ)/168755200) = (612187830727:ℝ)/295253868024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2610
  · change lowerPayment 2611 ≤ lowerValue ((point 2 split 4096 2611+point 2 split 4096 2612)/2)
    have hp : lowerPayment 2611 = (287063217784:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2611+point 2 split 4096 2612)/2 = (489661613:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489661613:ℝ)/168755200)/ClassicalSixthBranch.v ((489661613:ℝ)/168755200) = (612110517053:ℝ)/295205860136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2611
  · change lowerPayment 2612 ≤ lowerValue ((point 2 split 4096 2612+point 2 split 4096 2613)/2)
    have hp : lowerPayment 2612 = (287150995821:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2612+point 2 split 4096 2613)/2 = (19588795:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19588795:ℝ)/6750208)/ClassicalSixthBranch.v ((19588795:ℝ)/6750208) = (612033203379:ℝ)/295157852248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2612
  · change lowerPayment 2613 ≤ lowerValue ((point 2 split 4096 2613+point 2 split 4096 2614)/2)
    have hp : lowerPayment 2613 = (287238773020:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2613+point 2 split 4096 2614)/2 = (489778137:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489778137:ℝ)/168755200)/ClassicalSixthBranch.v ((489778137:ℝ)/168755200) = (122391177941:ℝ)/59021968872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2613
  · change lowerPayment 2614 ≤ lowerValue ((point 2 split 4096 2614+point 2 split 4096 2615)/2)
    have hp : lowerPayment 2614 = (287326549397:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2614+point 2 split 4096 2615)/2 = (489836399:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489836399:ℝ)/168755200)/ClassicalSixthBranch.v ((489836399:ℝ)/168755200) = (611878576031:ℝ)/295061836472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2614
  · change lowerPayment 2615 ≤ lowerValue ((point 2 split 4096 2615+point 2 split 4096 2616)/2)
    have hp : lowerPayment 2615 = (287414324965:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2615+point 2 split 4096 2616)/2 = (489894661:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489894661:ℝ)/168755200)/ClassicalSixthBranch.v ((489894661:ℝ)/168755200) = (611801262357:ℝ)/295013828584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2615
  · change lowerPayment 2616 ≤ lowerValue ((point 2 split 4096 2616+point 2 split 4096 2617)/2)
    have hp : lowerPayment 2616 = (287502099740:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2616+point 2 split 4096 2617)/2 = (489952923:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489952923:ℝ)/168755200)/ClassicalSixthBranch.v ((489952923:ℝ)/168755200) = (611723948683:ℝ)/294965820696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2616
  · change lowerPayment 2617 ≤ lowerValue ((point 2 split 4096 2617+point 2 split 4096 2618)/2)
    have hp : lowerPayment 2617 = (287589873734:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2617+point 2 split 4096 2618)/2 = (98002237:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98002237:ℝ)/33751040)/ClassicalSixthBranch.v ((98002237:ℝ)/33751040) = (611646635009:ℝ)/294917812808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2617
  · change lowerPayment 2618 ≤ lowerValue ((point 2 split 4096 2618+point 2 split 4096 2619)/2)
    have hp : lowerPayment 2618 = (287677646963:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2618+point 2 split 4096 2619)/2 = (490069447:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((490069447:ℝ)/168755200)/ClassicalSixthBranch.v ((490069447:ℝ)/168755200) = (122313864267:ℝ)/58973960984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2618
  · change lowerPayment 2619 ≤ lowerValue ((point 2 split 4096 2619+point 2 split 4096 2620)/2)
    have hp : lowerPayment 2619 = (287765419441:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2619+point 2 split 4096 2620)/2 = (490127709:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((490127709:ℝ)/168755200)/ClassicalSixthBranch.v ((490127709:ℝ)/168755200) = (611492007661:ℝ)/294821797032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2619
  · change lowerPayment 2620 ≤ lowerValue ((point 2 split 4096 2620+point 2 split 4096 2621)/2)
    have hp : lowerPayment 2620 = (287853191183:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2620+point 2 split 4096 2621)/2 = (490185971:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((490185971:ℝ)/168755200)/ClassicalSixthBranch.v ((490185971:ℝ)/168755200) = (611414693987:ℝ)/294773789144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2620
  · change lowerPayment 2621 ≤ lowerValue ((point 2 split 4096 2621+point 2 split 4096 2622)/2)
    have hp : lowerPayment 2621 = (287940962201:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2621+point 2 split 4096 2622)/2 = (490244233:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((490244233:ℝ)/168755200)/ClassicalSixthBranch.v ((490244233:ℝ)/168755200) = (611337380313:ℝ)/294725781256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2621
  · change lowerPayment 2622 ≤ lowerValue ((point 2 split 4096 2622+point 2 split 4096 2623)/2)
    have hp : lowerPayment 2622 = (288028732512:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2622+point 2 split 4096 2623)/2 = (98060499:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98060499:ℝ)/33751040)/ClassicalSixthBranch.v ((98060499:ℝ)/33751040) = (611260066639:ℝ)/294677773368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2622
  · change lowerPayment 2623 ≤ lowerValue ((point 2 split 4096 2623+point 2 split 4096 2624)/2)
    have hp : lowerPayment 2623 = (288116502128:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2623+point 2 split 4096 2624)/2 = (490360757:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((490360757:ℝ)/168755200)/ClassicalSixthBranch.v ((490360757:ℝ)/168755200) = (122236550593:ℝ)/58925953096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2623
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_163
