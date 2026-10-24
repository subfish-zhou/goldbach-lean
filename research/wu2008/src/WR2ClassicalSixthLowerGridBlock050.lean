import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints050
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_050 (j : Fin 16) : lowerPayment (16*50+j.val) ≤
    lowerValue ((point 2 split 4096 (16*50+j.val)+point 2 split 4096 (16*50+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 800 ≤ lowerValue ((point 2 split 4096 800+point 2 split 4096 801)/2)
    have hp : lowerPayment 800 = (110489793392:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 800+point 2 split 4096 801)/2 = (384149131:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384149131:ℝ)/168755200)/ClassicalSixthBranch.v ((384149131:ℝ)/168755200) = (752125580667:ℝ)/382148145304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_800
  · change lowerPayment 801 ≤ lowerValue ((point 2 split 4096 801+point 2 split 4096 802)/2)
    have hp : lowerPayment 801 = (110607970098:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 801+point 2 split 4096 802)/2 = (384207393:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384207393:ℝ)/168755200)/ClassicalSixthBranch.v ((384207393:ℝ)/168755200) = (752048266993:ℝ)/382100137416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_801
  · change lowerPayment 802 ≤ lowerValue ((point 2 split 4096 802+point 2 split 4096 803)/2)
    have hp : lowerPayment 802 = (110726108349:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 802+point 2 split 4096 803)/2 = (76853131:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((76853131:ℝ)/33751040)/ClassicalSixthBranch.v ((76853131:ℝ)/33751040) = (751970953319:ℝ)/382052129528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_802
  · change lowerPayment 803 ≤ lowerValue ((point 2 split 4096 803+point 2 split 4096 804)/2)
    have hp : lowerPayment 803 = (110844208179:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 803+point 2 split 4096 804)/2 = (384323917:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384323917:ℝ)/168755200)/ClassicalSixthBranch.v ((384323917:ℝ)/168755200) = (150378727929:ℝ)/76400824328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_803
  · change lowerPayment 804 ≤ lowerValue ((point 2 split 4096 804+point 2 split 4096 805)/2)
    have hp : lowerPayment 804 = (110962269621:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 804+point 2 split 4096 805)/2 = (384382179:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384382179:ℝ)/168755200)/ClassicalSixthBranch.v ((384382179:ℝ)/168755200) = (751816325971:ℝ)/381956113752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_804
  · change lowerPayment 805 ≤ lowerValue ((point 2 split 4096 805+point 2 split 4096 806)/2)
    have hp : lowerPayment 805 = (111080292712:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 805+point 2 split 4096 806)/2 = (384440441:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384440441:ℝ)/168755200)/ClassicalSixthBranch.v ((384440441:ℝ)/168755200) = (751739012297:ℝ)/381908105864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_805
  · change lowerPayment 806 ≤ lowerValue ((point 2 split 4096 806+point 2 split 4096 807)/2)
    have hp : lowerPayment 806 = (111198277484:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 806+point 2 split 4096 807)/2 = (384498703:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384498703:ℝ)/168755200)/ClassicalSixthBranch.v ((384498703:ℝ)/168755200) = (751661698623:ℝ)/381860097976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_806
  · change lowerPayment 807 ≤ lowerValue ((point 2 split 4096 807+point 2 split 4096 808)/2)
    have hp : lowerPayment 807 = (111316223973:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 807+point 2 split 4096 808)/2 = (76911393:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((76911393:ℝ)/33751040)/ClassicalSixthBranch.v ((76911393:ℝ)/33751040) = (751584384949:ℝ)/381812090088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_807
  · change lowerPayment 808 ≤ lowerValue ((point 2 split 4096 808+point 2 split 4096 809)/2)
    have hp : lowerPayment 808 = (111434132213:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 808+point 2 split 4096 809)/2 = (384615227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384615227:ℝ)/168755200)/ClassicalSixthBranch.v ((384615227:ℝ)/168755200) = (30060282851:ℝ)/15270563288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_808
  · change lowerPayment 809 ≤ lowerValue ((point 2 split 4096 809+point 2 split 4096 810)/2)
    have hp : lowerPayment 809 = (111552002239:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 809+point 2 split 4096 810)/2 = (384673489:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384673489:ℝ)/168755200)/ClassicalSixthBranch.v ((384673489:ℝ)/168755200) = (751429757601:ℝ)/381716074312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_809
  · change lowerPayment 810 ≤ lowerValue ((point 2 split 4096 810+point 2 split 4096 811)/2)
    have hp : lowerPayment 810 = (111669834084:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 810+point 2 split 4096 811)/2 = (384731751:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384731751:ℝ)/168755200)/ClassicalSixthBranch.v ((384731751:ℝ)/168755200) = (751352443927:ℝ)/381668066424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_810
  · change lowerPayment 811 ≤ lowerValue ((point 2 split 4096 811+point 2 split 4096 812)/2)
    have hp : lowerPayment 811 = (111787627783:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 811+point 2 split 4096 812)/2 = (384790013:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384790013:ℝ)/168755200)/ClassicalSixthBranch.v ((384790013:ℝ)/168755200) = (751275130253:ℝ)/381620058536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_811
  · change lowerPayment 812 ≤ lowerValue ((point 2 split 4096 812+point 2 split 4096 813)/2)
    have hp : lowerPayment 812 = (111905383370:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 812+point 2 split 4096 813)/2 = (15393931:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15393931:ℝ)/6750208)/ClassicalSixthBranch.v ((15393931:ℝ)/6750208) = (751197816579:ℝ)/381572050648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_812
  · change lowerPayment 813 ≤ lowerValue ((point 2 split 4096 813+point 2 split 4096 814)/2)
    have hp : lowerPayment 813 = (112023100880:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 813+point 2 split 4096 814)/2 = (384906537:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384906537:ℝ)/168755200)/ClassicalSixthBranch.v ((384906537:ℝ)/168755200) = (150224100581:ℝ)/76304808552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_813
  · change lowerPayment 814 ≤ lowerValue ((point 2 split 4096 814+point 2 split 4096 815)/2)
    have hp : lowerPayment 814 = (112140780347:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 814+point 2 split 4096 815)/2 = (384964799:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((384964799:ℝ)/168755200)/ClassicalSixthBranch.v ((384964799:ℝ)/168755200) = (751043189231:ℝ)/381476034872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_814
  · change lowerPayment 815 ≤ lowerValue ((point 2 split 4096 815+point 2 split 4096 816)/2)
    have hp : lowerPayment 815 = (112258421805:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 815+point 2 split 4096 816)/2 = (385023061:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385023061:ℝ)/168755200)/ClassicalSixthBranch.v ((385023061:ℝ)/168755200) = (750965875557:ℝ)/381428026984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_815
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_050
