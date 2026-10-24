import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints213
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_213 (j : Fin 16) : lowerPayment (16*213+j.val) ≤
    lowerValue ((point 2 split 4096 (16*213+j.val)+point 2 split 4096 (16*213+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3408 ≤ lowerValue ((point 2 split 4096 3408+point 2 split 4096 3409)/2)
    have hp : lowerPayment 3408 = (357949737208:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3408+point 2 split 4096 3409)/2 = (536096427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536096427:ℝ)/168755200)/ClassicalSixthBranch.v ((536096427:ℝ)/168755200) = (22019660755:ℝ)/10277742936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3408
  · change lowerPayment 3409 ≤ lowerValue ((point 2 split 4096 3409+point 2 split 4096 3410)/2)
    have hp : lowerPayment 3409 = (358041359974:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3409+point 2 split 4096 3410)/2 = (536154689:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536154689:ℝ)/168755200)/ClassicalSixthBranch.v ((536154689:ℝ)/168755200) = (550414205201:ℝ)/256895565512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3409
  · change lowerPayment 3410 ≤ lowerValue ((point 2 split 4096 3410+point 2 split 4096 3411)/2)
    have hp : lowerPayment 3410 = (358132993348:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3410+point 2 split 4096 3411)/2 = (536212951:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536212951:ℝ)/168755200)/ClassicalSixthBranch.v ((536212951:ℝ)/168755200) = (550336891527:ℝ)/256847557624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3410
  · change lowerPayment 3411 ≤ lowerValue ((point 2 split 4096 3411+point 2 split 4096 3412)/2)
    have hp : lowerPayment 3411 = (358224637345:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3411+point 2 split 4096 3412)/2 = (536271213:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536271213:ℝ)/168755200)/ClassicalSixthBranch.v ((536271213:ℝ)/168755200) = (550259577853:ℝ)/256799549736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3411
  · change lowerPayment 3412 ≤ lowerValue ((point 2 split 4096 3412+point 2 split 4096 3413)/2)
    have hp : lowerPayment 3412 = (358316291981:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3412+point 2 split 4096 3413)/2 = (21453179:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21453179:ℝ)/6750208)/ClassicalSixthBranch.v ((21453179:ℝ)/6750208) = (550182264179:ℝ)/256751541848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3412
  · change lowerPayment 3413 ≤ lowerValue ((point 2 split 4096 3413+point 2 split 4096 3414)/2)
    have hp : lowerPayment 3413 = (358407957270:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3413+point 2 split 4096 3414)/2 = (536387737:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536387737:ℝ)/168755200)/ClassicalSixthBranch.v ((536387737:ℝ)/168755200) = (110020990101:ℝ)/51340706792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3413
  · change lowerPayment 3414 ≤ lowerValue ((point 2 split 4096 3414+point 2 split 4096 3415)/2)
    have hp : lowerPayment 3414 = (358499633227:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3414+point 2 split 4096 3415)/2 = (536445999:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536445999:ℝ)/168755200)/ClassicalSixthBranch.v ((536445999:ℝ)/168755200) = (550027636831:ℝ)/256655526072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3414
  · change lowerPayment 3415 ≤ lowerValue ((point 2 split 4096 3415+point 2 split 4096 3416)/2)
    have hp : lowerPayment 3415 = (358591319868:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3415+point 2 split 4096 3416)/2 = (536504261:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536504261:ℝ)/168755200)/ClassicalSixthBranch.v ((536504261:ℝ)/168755200) = (549950323157:ℝ)/256607518184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3415
  · change lowerPayment 3416 ≤ lowerValue ((point 2 split 4096 3416+point 2 split 4096 3417)/2)
    have hp : lowerPayment 3416 = (358683017208:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3416+point 2 split 4096 3417)/2 = (536562523:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536562523:ℝ)/168755200)/ClassicalSixthBranch.v ((536562523:ℝ)/168755200) = (549873009483:ℝ)/256559510296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3416
  · change lowerPayment 3417 ≤ lowerValue ((point 2 split 4096 3417+point 2 split 4096 3418)/2)
    have hp : lowerPayment 3417 = (358774725262:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3417+point 2 split 4096 3418)/2 = (107324157:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107324157:ℝ)/33751040)/ClassicalSixthBranch.v ((107324157:ℝ)/33751040) = (549795695809:ℝ)/256511502408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3417
  · change lowerPayment 3418 ≤ lowerValue ((point 2 split 4096 3418+point 2 split 4096 3419)/2)
    have hp : lowerPayment 3418 = (358866444045:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3418+point 2 split 4096 3419)/2 = (536679047:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536679047:ℝ)/168755200)/ClassicalSixthBranch.v ((536679047:ℝ)/168755200) = (109943676427:ℝ)/51292698904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3418
  · change lowerPayment 3419 ≤ lowerValue ((point 2 split 4096 3419+point 2 split 4096 3420)/2)
    have hp : lowerPayment 3419 = (358958173573:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3419+point 2 split 4096 3420)/2 = (536737309:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536737309:ℝ)/168755200)/ClassicalSixthBranch.v ((536737309:ℝ)/168755200) = (549641068461:ℝ)/256415486632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3419
  · change lowerPayment 3420 ≤ lowerValue ((point 2 split 4096 3420+point 2 split 4096 3421)/2)
    have hp : lowerPayment 3420 = (359049913860:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3420+point 2 split 4096 3421)/2 = (536795571:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536795571:ℝ)/168755200)/ClassicalSixthBranch.v ((536795571:ℝ)/168755200) = (549563754787:ℝ)/256367478744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3420
  · change lowerPayment 3421 ≤ lowerValue ((point 2 split 4096 3421+point 2 split 4096 3422)/2)
    have hp : lowerPayment 3421 = (359141664922:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3421+point 2 split 4096 3422)/2 = (536853833:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536853833:ℝ)/168755200)/ClassicalSixthBranch.v ((536853833:ℝ)/168755200) = (549486441113:ℝ)/256319470856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3421
  · change lowerPayment 3422 ≤ lowerValue ((point 2 split 4096 3422+point 2 split 4096 3423)/2)
    have hp : lowerPayment 3422 = (359233426774:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3422+point 2 split 4096 3423)/2 = (107382419:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((107382419:ℝ)/33751040)/ClassicalSixthBranch.v ((107382419:ℝ)/33751040) = (549409127439:ℝ)/256271462968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3422
  · change lowerPayment 3423 ≤ lowerValue ((point 2 split 4096 3423+point 2 split 4096 3424)/2)
    have hp : lowerPayment 3423 = (359325199431:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3423+point 2 split 4096 3424)/2 = (536970357:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((536970357:ℝ)/168755200)/ClassicalSixthBranch.v ((536970357:ℝ)/168755200) = (109866362753:ℝ)/51244691016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3423
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_213
