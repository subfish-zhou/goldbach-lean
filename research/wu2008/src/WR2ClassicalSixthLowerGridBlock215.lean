import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints215
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_215 (j : Fin 16) : lowerPayment (16*215+j.val) ≤
    lowerValue ((point 2 split 4096 (16*215+j.val)+point 2 split 4096 (16*215+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3440 ≤ lowerValue ((point 2 split 4096 3440+point 2 split 4096 3441)/2)
    have hp : lowerPayment 3440 = (360887002502:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3440+point 2 split 4096 3441)/2 = (537960811:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((537960811:ℝ)/168755200)/ClassicalSixthBranch.v ((537960811:ℝ)/168755200) = (548017481307:ℝ)/255407320984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3440
  · change lowerPayment 3441 ≤ lowerValue ((point 2 split 4096 3441+point 2 split 4096 3442)/2)
    have hp : lowerPayment 3441 = (360978972250:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3441+point 2 split 4096 3442)/2 = (538019073:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((538019073:ℝ)/168755200)/ClassicalSixthBranch.v ((538019073:ℝ)/168755200) = (547940167633:ℝ)/255359313096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3441
  · change lowerPayment 3442 ≤ lowerValue ((point 2 split 4096 3442+point 2 split 4096 3443)/2)
    have hp : lowerPayment 3442 = (361070953093:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3442+point 2 split 4096 3443)/2 = (107615467:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107615467:ℝ)/33751040)/ClassicalSixthBranch.v ((107615467:ℝ)/33751040) = (547862853959:ℝ)/255311305208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3442
  · change lowerPayment 3443 ≤ lowerValue ((point 2 split 4096 3443+point 2 split 4096 3444)/2)
    have hp : lowerPayment 3443 = (361162945046:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3443+point 2 split 4096 3444)/2 = (538135597:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((538135597:ℝ)/168755200)/ClassicalSixthBranch.v ((538135597:ℝ)/168755200) = (109557108057:ℝ)/51052659464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3443
  · change lowerPayment 3444 ≤ lowerValue ((point 2 split 4096 3444+point 2 split 4096 3445)/2)
    have hp : lowerPayment 3444 = (361254948123:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3444+point 2 split 4096 3445)/2 = (538193859:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((538193859:ℝ)/168755200)/ClassicalSixthBranch.v ((538193859:ℝ)/168755200) = (547708226611:ℝ)/255215289432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3444
  · change lowerPayment 3445 ≤ lowerValue ((point 2 split 4096 3445+point 2 split 4096 3446)/2)
    have hp : lowerPayment 3445 = (361346962340:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3445+point 2 split 4096 3446)/2 = (538252121:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((538252121:ℝ)/168755200)/ClassicalSixthBranch.v ((538252121:ℝ)/168755200) = (547630912937:ℝ)/255167281544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3445
  · change lowerPayment 3446 ≤ lowerValue ((point 2 split 4096 3446+point 2 split 4096 3447)/2)
    have hp : lowerPayment 3446 = (361438987713:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3446+point 2 split 4096 3447)/2 = (538310383:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((538310383:ℝ)/168755200)/ClassicalSixthBranch.v ((538310383:ℝ)/168755200) = (547553599263:ℝ)/255119273656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3446
  · change lowerPayment 3447 ≤ lowerValue ((point 2 split 4096 3447+point 2 split 4096 3448)/2)
    have hp : lowerPayment 3447 = (361531024256:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3447+point 2 split 4096 3448)/2 = (107673729:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107673729:ℝ)/33751040)/ClassicalSixthBranch.v ((107673729:ℝ)/33751040) = (547476285589:ℝ)/255071265768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3447
  · change lowerPayment 3448 ≤ lowerValue ((point 2 split 4096 3448+point 2 split 4096 3449)/2)
    have hp : lowerPayment 3448 = (361623071985:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3448+point 2 split 4096 3449)/2 = (538426907:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((538426907:ℝ)/168755200)/ClassicalSixthBranch.v ((538426907:ℝ)/168755200) = (109479794383:ℝ)/51004651576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3448
  · change lowerPayment 3449 ≤ lowerValue ((point 2 split 4096 3449+point 2 split 4096 3450)/2)
    have hp : lowerPayment 3449 = (361715130916:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3449+point 2 split 4096 3450)/2 = (538485169:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((538485169:ℝ)/168755200)/ClassicalSixthBranch.v ((538485169:ℝ)/168755200) = (547321658241:ℝ)/254975249992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3449
  · change lowerPayment 3450 ≤ lowerValue ((point 2 split 4096 3450+point 2 split 4096 3451)/2)
    have hp : lowerPayment 3450 = (361807201063:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3450+point 2 split 4096 3451)/2 = (5228577:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((5228577:ℝ)/1638400)/ClassicalSixthBranch.v ((5228577:ℝ)/1638400) = (5313051889:ℝ)/2475021768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3450
  · change lowerPayment 3451 ≤ lowerValue ((point 2 split 4096 3451+point 2 split 4096 3452)/2)
    have hp : lowerPayment 3451 = (361899282442:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3451+point 2 split 4096 3452)/2 = (538601693:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((538601693:ℝ)/168755200)/ClassicalSixthBranch.v ((538601693:ℝ)/168755200) = (547167030893:ℝ)/254879234216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3451
  · change lowerPayment 3452 ≤ lowerValue ((point 2 split 4096 3452+point 2 split 4096 3453)/2)
    have hp : lowerPayment 3452 = (361991375067:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3452+point 2 split 4096 3453)/2 = (107731991:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107731991:ℝ)/33751040)/ClassicalSixthBranch.v ((107731991:ℝ)/33751040) = (547089717219:ℝ)/254831226328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3452
  · change lowerPayment 3453 ≤ lowerValue ((point 2 split 4096 3453+point 2 split 4096 3454)/2)
    have hp : lowerPayment 3453 = (362083478955:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3453+point 2 split 4096 3454)/2 = (538718217:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((538718217:ℝ)/168755200)/ClassicalSixthBranch.v ((538718217:ℝ)/168755200) = (109402480709:ℝ)/50956643688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3453
  · change lowerPayment 3454 ≤ lowerValue ((point 2 split 4096 3454+point 2 split 4096 3455)/2)
    have hp : lowerPayment 3454 = (362175594121:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3454+point 2 split 4096 3455)/2 = (538776479:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((538776479:ℝ)/168755200)/ClassicalSixthBranch.v ((538776479:ℝ)/168755200) = (546935089871:ℝ)/254735210552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3454
  · change lowerPayment 3455 ≤ lowerValue ((point 2 split 4096 3455+point 2 split 4096 3456)/2)
    have hp : lowerPayment 3455 = (362267720580:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3455+point 2 split 4096 3456)/2 = (538834741:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((538834741:ℝ)/168755200)/ClassicalSixthBranch.v ((538834741:ℝ)/168755200) = (546857776197:ℝ)/254687202664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3455
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_215
