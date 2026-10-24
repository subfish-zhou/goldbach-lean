import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints216
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_216 (j : Fin 16) : lowerPayment (16*216+j.val) ≤
    lowerValue ((point 2 split 4096 (16*216+j.val)+point 2 split 4096 (16*216+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3456 ≤ lowerValue ((point 2 split 4096 3456+point 2 split 4096 3457)/2)
    have hp : lowerPayment 3456 = (362359858347:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3456+point 2 split 4096 3457)/2 = (538893003:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((538893003:ℝ)/168755200)/ClassicalSixthBranch.v ((538893003:ℝ)/168755200) = (546780462523:ℝ)/254639194776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3456
  · change lowerPayment 3457 ≤ lowerValue ((point 2 split 4096 3457+point 2 split 4096 3458)/2)
    have hp : lowerPayment 3457 = (362452007438:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3457+point 2 split 4096 3458)/2 = (107790253:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107790253:ℝ)/33751040)/ClassicalSixthBranch.v ((107790253:ℝ)/33751040) = (546703148849:ℝ)/254591186888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3457
  · change lowerPayment 3458 ≤ lowerValue ((point 2 split 4096 3458+point 2 split 4096 3459)/2)
    have hp : lowerPayment 3458 = (362544167868:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3458+point 2 split 4096 3459)/2 = (539009527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539009527:ℝ)/168755200)/ClassicalSixthBranch.v ((539009527:ℝ)/168755200) = (21865033407:ℝ)/10181727160 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3458
  · change lowerPayment 3459 ≤ lowerValue ((point 2 split 4096 3459+point 2 split 4096 3460)/2)
    have hp : lowerPayment 3459 = (362636339652:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3459+point 2 split 4096 3460)/2 = (539067789:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539067789:ℝ)/168755200)/ClassicalSixthBranch.v ((539067789:ℝ)/168755200) = (546548521501:ℝ)/254495171112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3459
  · change lowerPayment 3460 ≤ lowerValue ((point 2 split 4096 3460+point 2 split 4096 3461)/2)
    have hp : lowerPayment 3460 = (362728522806:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3460+point 2 split 4096 3461)/2 = (539126051:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539126051:ℝ)/168755200)/ClassicalSixthBranch.v ((539126051:ℝ)/168755200) = (546471207827:ℝ)/254447163224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3460
  · change lowerPayment 3461 ≤ lowerValue ((point 2 split 4096 3461+point 2 split 4096 3462)/2)
    have hp : lowerPayment 3461 = (362820717345:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3461+point 2 split 4096 3462)/2 = (539184313:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539184313:ℝ)/168755200)/ClassicalSixthBranch.v ((539184313:ℝ)/168755200) = (546393894153:ℝ)/254399155336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3461
  · change lowerPayment 3462 ≤ lowerValue ((point 2 split 4096 3462+point 2 split 4096 3463)/2)
    have hp : lowerPayment 3462 = (362912923284:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3462+point 2 split 4096 3463)/2 = (21569703:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21569703:ℝ)/6750208)/ClassicalSixthBranch.v ((21569703:ℝ)/6750208) = (546316580479:ℝ)/254351147448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3462
  · change lowerPayment 3463 ≤ lowerValue ((point 2 split 4096 3463+point 2 split 4096 3464)/2)
    have hp : lowerPayment 3463 = (363005140638:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3463+point 2 split 4096 3464)/2 = (539300837:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539300837:ℝ)/168755200)/ClassicalSixthBranch.v ((539300837:ℝ)/168755200) = (109247853361:ℝ)/50860627912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3463
  · change lowerPayment 3464 ≤ lowerValue ((point 2 split 4096 3464+point 2 split 4096 3465)/2)
    have hp : lowerPayment 3464 = (363097369424:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3464+point 2 split 4096 3465)/2 = (539359099:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539359099:ℝ)/168755200)/ClassicalSixthBranch.v ((539359099:ℝ)/168755200) = (546161953131:ℝ)/254255131672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3464
  · change lowerPayment 3465 ≤ lowerValue ((point 2 split 4096 3465+point 2 split 4096 3466)/2)
    have hp : lowerPayment 3465 = (363189609656:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3465+point 2 split 4096 3466)/2 = (539417361:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539417361:ℝ)/168755200)/ClassicalSixthBranch.v ((539417361:ℝ)/168755200) = (546084639457:ℝ)/254207123784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3465
  · change lowerPayment 3466 ≤ lowerValue ((point 2 split 4096 3466+point 2 split 4096 3467)/2)
    have hp : lowerPayment 3466 = (363281861350:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3466+point 2 split 4096 3467)/2 = (539475623:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539475623:ℝ)/168755200)/ClassicalSixthBranch.v ((539475623:ℝ)/168755200) = (546007325783:ℝ)/254159115896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3466
  · change lowerPayment 3467 ≤ lowerValue ((point 2 split 4096 3467+point 2 split 4096 3468)/2)
    have hp : lowerPayment 3467 = (363374124520:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3467+point 2 split 4096 3468)/2 = (107906777:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107906777:ℝ)/33751040)/ClassicalSixthBranch.v ((107906777:ℝ)/33751040) = (545930012109:ℝ)/254111108008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3467
  · change lowerPayment 3468 ≤ lowerValue ((point 2 split 4096 3468+point 2 split 4096 3469)/2)
    have hp : lowerPayment 3468 = (363466399184:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3468+point 2 split 4096 3469)/2 = (539592147:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539592147:ℝ)/168755200)/ClassicalSixthBranch.v ((539592147:ℝ)/168755200) = (109170539687:ℝ)/50812620024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3468
  · change lowerPayment 3469 ≤ lowerValue ((point 2 split 4096 3469+point 2 split 4096 3470)/2)
    have hp : lowerPayment 3469 = (363558685355:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3469+point 2 split 4096 3470)/2 = (539650409:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539650409:ℝ)/168755200)/ClassicalSixthBranch.v ((539650409:ℝ)/168755200) = (545775384761:ℝ)/254015092232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3469
  · change lowerPayment 3470 ≤ lowerValue ((point 2 split 4096 3470+point 2 split 4096 3471)/2)
    have hp : lowerPayment 3470 = (363650983049:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3470+point 2 split 4096 3471)/2 = (539708671:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539708671:ℝ)/168755200)/ClassicalSixthBranch.v ((539708671:ℝ)/168755200) = (545698071087:ℝ)/253967084344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3470
  · change lowerPayment 3471 ≤ lowerValue ((point 2 split 4096 3471+point 2 split 4096 3472)/2)
    have hp : lowerPayment 3471 = (363743292282:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3471+point 2 split 4096 3472)/2 = (539766933:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((539766933:ℝ)/168755200)/ClassicalSixthBranch.v ((539766933:ℝ)/168755200) = (545620757413:ℝ)/253919076456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3471
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_216
