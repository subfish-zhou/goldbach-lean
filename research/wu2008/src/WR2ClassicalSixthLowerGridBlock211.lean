import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints211
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_211 (j : Fin 16) : lowerPayment (16*211+j.val) ≤
    lowerValue ((point 2 split 4096 (16*211+j.val)+point 2 split 4096 (16*211+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3376 ≤ lowerValue ((point 2 split 4096 3376+point 2 split 4096 3377)/2)
    have hp : lowerPayment 3376 = (355023319349:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3376+point 2 split 4096 3377)/2 = (534232043:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534232043:ℝ)/168755200)/ClassicalSixthBranch.v ((534232043:ℝ)/168755200) = (552965556443:ℝ)/258479825816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3376
  · change lowerPayment 3377 ≤ lowerValue ((point 2 split 4096 3377+point 2 split 4096 3378)/2)
    have hp : lowerPayment 3377 = (355114610628:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3377+point 2 split 4096 3378)/2 = (106858061:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((106858061:ℝ)/33751040)/ClassicalSixthBranch.v ((106858061:ℝ)/33751040) = (552888242769:ℝ)/258431817928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3377
  · change lowerPayment 3378 ≤ lowerValue ((point 2 split 4096 3378+point 2 split 4096 3379)/2)
    have hp : lowerPayment 3378 = (355205912032:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3378+point 2 split 4096 3379)/2 = (534348567:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534348567:ℝ)/168755200)/ClassicalSixthBranch.v ((534348567:ℝ)/168755200) = (110562185819:ℝ)/51676762008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3378
  · change lowerPayment 3379 ≤ lowerValue ((point 2 split 4096 3379+point 2 split 4096 3380)/2)
    have hp : lowerPayment 3379 = (355297223577:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3379+point 2 split 4096 3380)/2 = (534406829:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534406829:ℝ)/168755200)/ClassicalSixthBranch.v ((534406829:ℝ)/168755200) = (552733615421:ℝ)/258335802152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3379
  · change lowerPayment 3380 ≤ lowerValue ((point 2 split 4096 3380+point 2 split 4096 3381)/2)
    have hp : lowerPayment 3380 = (355388545278:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3380+point 2 split 4096 3381)/2 = (534465091:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534465091:ℝ)/168755200)/ClassicalSixthBranch.v ((534465091:ℝ)/168755200) = (552656301747:ℝ)/258287794264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3380
  · change lowerPayment 3381 ≤ lowerValue ((point 2 split 4096 3381+point 2 split 4096 3382)/2)
    have hp : lowerPayment 3381 = (355479877150:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3381+point 2 split 4096 3382)/2 = (534523353:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534523353:ℝ)/168755200)/ClassicalSixthBranch.v ((534523353:ℝ)/168755200) = (552578988073:ℝ)/258239786376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3381
  · change lowerPayment 3382 ≤ lowerValue ((point 2 split 4096 3382+point 2 split 4096 3383)/2)
    have hp : lowerPayment 3382 = (355571219207:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3382+point 2 split 4096 3383)/2 = (106916323:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((106916323:ℝ)/33751040)/ClassicalSixthBranch.v ((106916323:ℝ)/33751040) = (552501674399:ℝ)/258191778488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3382
  · change lowerPayment 3383 ≤ lowerValue ((point 2 split 4096 3383+point 2 split 4096 3384)/2)
    have hp : lowerPayment 3383 = (355662571465:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3383+point 2 split 4096 3384)/2 = (534639877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534639877:ℝ)/168755200)/ClassicalSixthBranch.v ((534639877:ℝ)/168755200) = (22096974429:ℝ)/10325750824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3383
  · change lowerPayment 3384 ≤ lowerValue ((point 2 split 4096 3384+point 2 split 4096 3385)/2)
    have hp : lowerPayment 3384 = (355753933939:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3384+point 2 split 4096 3385)/2 = (534698139:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534698139:ℝ)/168755200)/ClassicalSixthBranch.v ((534698139:ℝ)/168755200) = (552347047051:ℝ)/258095762712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3384
  · change lowerPayment 3385 ≤ lowerValue ((point 2 split 4096 3385+point 2 split 4096 3386)/2)
    have hp : lowerPayment 3385 = (355845306644:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3385+point 2 split 4096 3386)/2 = (534756401:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534756401:ℝ)/168755200)/ClassicalSixthBranch.v ((534756401:ℝ)/168755200) = (552269733377:ℝ)/258047754824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3385
  · change lowerPayment 3386 ≤ lowerValue ((point 2 split 4096 3386+point 2 split 4096 3387)/2)
    have hp : lowerPayment 3386 = (355936689594:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3386+point 2 split 4096 3387)/2 = (534814663:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534814663:ℝ)/168755200)/ClassicalSixthBranch.v ((534814663:ℝ)/168755200) = (552192419703:ℝ)/257999746936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3386
  · change lowerPayment 3387 ≤ lowerValue ((point 2 split 4096 3387+point 2 split 4096 3388)/2)
    have hp : lowerPayment 3387 = (356028082806:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3387+point 2 split 4096 3388)/2 = (21394917:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21394917:ℝ)/6750208)/ClassicalSixthBranch.v ((21394917:ℝ)/6750208) = (552115106029:ℝ)/257951739048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3387
  · change lowerPayment 3388 ≤ lowerValue ((point 2 split 4096 3388+point 2 split 4096 3389)/2)
    have hp : lowerPayment 3388 = (356119486293:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3388+point 2 split 4096 3389)/2 = (534931187:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534931187:ℝ)/168755200)/ClassicalSixthBranch.v ((534931187:ℝ)/168755200) = (110407558471:ℝ)/51580746232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3388
  · change lowerPayment 3389 ≤ lowerValue ((point 2 split 4096 3389+point 2 split 4096 3390)/2)
    have hp : lowerPayment 3389 = (356210900072:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3389+point 2 split 4096 3390)/2 = (534989449:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((534989449:ℝ)/168755200)/ClassicalSixthBranch.v ((534989449:ℝ)/168755200) = (551960478681:ℝ)/257855723272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3389
  · change lowerPayment 3390 ≤ lowerValue ((point 2 split 4096 3390+point 2 split 4096 3391)/2)
    have hp : lowerPayment 3390 = (356302324157:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3390+point 2 split 4096 3391)/2 = (535047711:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535047711:ℝ)/168755200)/ClassicalSixthBranch.v ((535047711:ℝ)/168755200) = (551883165007:ℝ)/257807715384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3390
  · change lowerPayment 3391 ≤ lowerValue ((point 2 split 4096 3391+point 2 split 4096 3392)/2)
    have hp : lowerPayment 3391 = (356393758562:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3391+point 2 split 4096 3392)/2 = (535105973:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((535105973:ℝ)/168755200)/ClassicalSixthBranch.v ((535105973:ℝ)/168755200) = (551805851333:ℝ)/257759707496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3391
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_211
