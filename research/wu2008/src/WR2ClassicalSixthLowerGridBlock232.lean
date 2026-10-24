import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints232
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_232 (j : Fin 16) : lowerPayment (16*232+j.val) ≤
    lowerValue ((point 2 split 4096 (16*232+j.val)+point 2 split 4096 (16*232+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3712 ≤ lowerValue ((point 2 split 4096 3712+point 2 split 4096 3713)/2)
    have hp : lowerPayment 3712 = (386363295334:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3712+point 2 split 4096 3713)/2 = (22152323:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22152323:ℝ)/6750208)/ClassicalSixthBranch.v ((22152323:ℝ)/6750208) = (526988161979:ℝ)/242349175448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3712
  · change lowerPayment 3713 ≤ lowerValue ((point 2 split 4096 3713+point 2 split 4096 3714)/2)
    have hp : lowerPayment 3713 = (386458860548:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3713+point 2 split 4096 3714)/2 = (553866337:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553866337:ℝ)/168755200)/ClassicalSixthBranch.v ((553866337:ℝ)/168755200) = (105382169661:ℝ)/48460233512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3713
  · change lowerPayment 3714 ≤ lowerValue ((point 2 split 4096 3714+point 2 split 4096 3715)/2)
    have hp : lowerPayment 3714 = (386554441184:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3714+point 2 split 4096 3715)/2 = (553924599:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553924599:ℝ)/168755200)/ClassicalSixthBranch.v ((553924599:ℝ)/168755200) = (526833534631:ℝ)/242253159672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3714
  · change lowerPayment 3715 ≤ lowerValue ((point 2 split 4096 3715+point 2 split 4096 3716)/2)
    have hp : lowerPayment 3715 = (386650037260:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3715+point 2 split 4096 3716)/2 = (553982861:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((553982861:ℝ)/168755200)/ClassicalSixthBranch.v ((553982861:ℝ)/168755200) = (526756220957:ℝ)/242205151784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3715
  · change lowerPayment 3716 ≤ lowerValue ((point 2 split 4096 3716+point 2 split 4096 3717)/2)
    have hp : lowerPayment 3716 = (386745648792:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3716+point 2 split 4096 3717)/2 = (554041123:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554041123:ℝ)/168755200)/ClassicalSixthBranch.v ((554041123:ℝ)/168755200) = (526678907283:ℝ)/242157143896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3716
  · change lowerPayment 3717 ≤ lowerValue ((point 2 split 4096 3717+point 2 split 4096 3718)/2)
    have hp : lowerPayment 3717 = (386841275797:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3717+point 2 split 4096 3718)/2 = (110819877:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110819877:ℝ)/33751040)/ClassicalSixthBranch.v ((110819877:ℝ)/33751040) = (526601593609:ℝ)/242109136008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3717
  · change lowerPayment 3718 ≤ lowerValue ((point 2 split 4096 3718+point 2 split 4096 3719)/2)
    have hp : lowerPayment 3718 = (386936918291:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3718+point 2 split 4096 3719)/2 = (554157647:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554157647:ℝ)/168755200)/ClassicalSixthBranch.v ((554157647:ℝ)/168755200) = (105304855987:ℝ)/48412225624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3718
  · change lowerPayment 3719 ≤ lowerValue ((point 2 split 4096 3719+point 2 split 4096 3720)/2)
    have hp : lowerPayment 3719 = (387032576291:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3719+point 2 split 4096 3720)/2 = (554215909:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554215909:ℝ)/168755200)/ClassicalSixthBranch.v ((554215909:ℝ)/168755200) = (526446966261:ℝ)/242013120232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3719
  · change lowerPayment 3720 ≤ lowerValue ((point 2 split 4096 3720+point 2 split 4096 3721)/2)
    have hp : lowerPayment 3720 = (387128249815:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3720+point 2 split 4096 3721)/2 = (554274171:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554274171:ℝ)/168755200)/ClassicalSixthBranch.v ((554274171:ℝ)/168755200) = (526369652587:ℝ)/241965112344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3720
  · change lowerPayment 3721 ≤ lowerValue ((point 2 split 4096 3721+point 2 split 4096 3722)/2)
    have hp : lowerPayment 3721 = (387223938877:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3721+point 2 split 4096 3722)/2 = (554332433:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554332433:ℝ)/168755200)/ClassicalSixthBranch.v ((554332433:ℝ)/168755200) = (526292338913:ℝ)/241917104456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3721
  · change lowerPayment 3722 ≤ lowerValue ((point 2 split 4096 3722+point 2 split 4096 3723)/2)
    have hp : lowerPayment 3722 = (387319643497:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3722+point 2 split 4096 3723)/2 = (110878139:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110878139:ℝ)/33751040)/ClassicalSixthBranch.v ((110878139:ℝ)/33751040) = (526215025239:ℝ)/241869096568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3722
  · change lowerPayment 3723 ≤ lowerValue ((point 2 split 4096 3723+point 2 split 4096 3724)/2)
    have hp : lowerPayment 3723 = (387415363689:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3723+point 2 split 4096 3724)/2 = (554448957:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554448957:ℝ)/168755200)/ClassicalSixthBranch.v ((554448957:ℝ)/168755200) = (105227542313:ℝ)/48364217736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3723
  · change lowerPayment 3724 ≤ lowerValue ((point 2 split 4096 3724+point 2 split 4096 3725)/2)
    have hp : lowerPayment 3724 = (387511099471:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3724+point 2 split 4096 3725)/2 = (554507219:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554507219:ℝ)/168755200)/ClassicalSixthBranch.v ((554507219:ℝ)/168755200) = (526060397891:ℝ)/241773080792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3724
  · change lowerPayment 3725 ≤ lowerValue ((point 2 split 4096 3725+point 2 split 4096 3726)/2)
    have hp : lowerPayment 3725 = (387606850859:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3725+point 2 split 4096 3726)/2 = (554565481:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554565481:ℝ)/168755200)/ClassicalSixthBranch.v ((554565481:ℝ)/168755200) = (525983084217:ℝ)/241725072904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3725
  · change lowerPayment 3726 ≤ lowerValue ((point 2 split 4096 3726+point 2 split 4096 3727)/2)
    have hp : lowerPayment 3726 = (387702617871:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3726+point 2 split 4096 3727)/2 = (554623743:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((554623743:ℝ)/168755200)/ClassicalSixthBranch.v ((554623743:ℝ)/168755200) = (525905770543:ℝ)/241677065016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3726
  · change lowerPayment 3727 ≤ lowerValue ((point 2 split 4096 3727+point 2 split 4096 3728)/2)
    have hp : lowerPayment 3727 = (387798400523:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3727+point 2 split 4096 3728)/2 = (110936401:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((110936401:ℝ)/33751040)/ClassicalSixthBranch.v ((110936401:ℝ)/33751040) = (525828456869:ℝ)/241629057128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3727
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_232
