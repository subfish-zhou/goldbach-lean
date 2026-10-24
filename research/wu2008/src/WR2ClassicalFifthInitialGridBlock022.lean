import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints022
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_022 (j : Fin 16) : initialPayment (16*22+j.val) ≤
    initialValue ((point lo 4 1024 (16*22+j.val)+point lo 4 1024 (16*22+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 352 ≤ initialValue ((point lo 4 1024 352+point lo 4 1024 353)/2)
    have hp : initialPayment 352 = (156389024960:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 352+point lo 4 1024 353)/2 = (152546533:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152546533:ℝ)/42188800) = (13588480:ℝ)/11886751 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_352
  · change initialPayment 353 ≤ initialValue ((point lo 4 1024 353+point lo 4 1024 354)/2)
    have hp : initialPayment 353 = (156904415668:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 353+point lo 4 1024 354)/2 = (152570671:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152570671:ℝ)/42188800) = (67942400:ℝ)/59409617 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_353
  · change initialPayment 354 ≤ initialValue ((point lo 4 1024 354+point lo 4 1024 355)/2)
    have hp : initialPayment 354 = (157420249300:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 354+point lo 4 1024 355)/2 = (1481503:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((1481503:ℝ)/409600) = (67942400:ℝ)/59385479 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_354
  · change initialPayment 355 ≤ initialValue ((point lo 4 1024 355+point lo 4 1024 356)/2)
    have hp : initialPayment 355 = (157936526210:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 355+point lo 4 1024 356)/2 = (152618947:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152618947:ℝ)/42188800) = (67942400:ℝ)/59361341 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_355
  · change initialPayment 356 ≤ initialValue ((point lo 4 1024 356+point lo 4 1024 357)/2)
    have hp : initialPayment 356 = (158453246754:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 356+point lo 4 1024 357)/2 = (30528617:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30528617:ℝ)/8437760) = (67942400:ℝ)/59337203 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_356
  · change initialPayment 357 ≤ initialValue ((point lo 4 1024 357+point lo 4 1024 358)/2)
    have hp : initialPayment 357 = (158970411290:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 357+point lo 4 1024 358)/2 = (152667223:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152667223:ℝ)/42188800) = (13588480:ℝ)/11862613 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_357
  · change initialPayment 358 ≤ initialValue ((point lo 4 1024 358+point lo 4 1024 359)/2)
    have hp : initialPayment 358 = (159488020175:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 358+point lo 4 1024 359)/2 = (152691361:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152691361:ℝ)/42188800) = (67942400:ℝ)/59288927 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_358
  · change initialPayment 359 ≤ initialValue ((point lo 4 1024 359+point lo 4 1024 360)/2)
    have hp : initialPayment 359 = (160006073766:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 359+point lo 4 1024 360)/2 = (152715499:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152715499:ℝ)/42188800) = (67942400:ℝ)/59264789 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_359
  · change initialPayment 360 ≤ initialValue ((point lo 4 1024 360+point lo 4 1024 361)/2)
    have hp : initialPayment 360 = (160524572422:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 360+point lo 4 1024 361)/2 = (152739637:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152739637:ℝ)/42188800) = (67942400:ℝ)/59240651 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_360
  · change initialPayment 361 ≤ initialValue ((point lo 4 1024 361+point lo 4 1024 362)/2)
    have hp : initialPayment 361 = (161043516501:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 361+point lo 4 1024 362)/2 = (6110551:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6110551:ℝ)/1687552) = (67942400:ℝ)/59216513 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_361
  · change initialPayment 362 ≤ initialValue ((point lo 4 1024 362+point lo 4 1024 363)/2)
    have hp : initialPayment 362 = (161562906364:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 362+point lo 4 1024 363)/2 = (152787913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152787913:ℝ)/42188800) = (2717696:ℝ)/2367695 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_362
  · change initialPayment 363 ≤ initialValue ((point lo 4 1024 363+point lo 4 1024 364)/2)
    have hp : initialPayment 363 = (162082742369:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 363+point lo 4 1024 364)/2 = (152812051:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152812051:ℝ)/42188800) = (67942400:ℝ)/59168237 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_363
  · change initialPayment 364 ≤ initialValue ((point lo 4 1024 364+point lo 4 1024 365)/2)
    have hp : initialPayment 364 = (162603024877:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 364+point lo 4 1024 365)/2 = (152836189:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152836189:ℝ)/42188800) = (67942400:ℝ)/59144099 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_364
  · change initialPayment 365 ≤ initialValue ((point lo 4 1024 365+point lo 4 1024 366)/2)
    have hp : initialPayment 365 = (163123754250:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 365+point lo 4 1024 366)/2 = (152860327:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152860327:ℝ)/42188800) = (67942400:ℝ)/59119961 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_365
  · change initialPayment 366 ≤ initialValue ((point lo 4 1024 366+point lo 4 1024 367)/2)
    have hp : initialPayment 366 = (163644930848:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 366+point lo 4 1024 367)/2 = (30576893:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30576893:ℝ)/8437760) = (67942400:ℝ)/59095823 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_366
  · change initialPayment 367 ≤ initialValue ((point lo 4 1024 367+point lo 4 1024 368)/2)
    have hp : initialPayment 367 = (164166555033:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 367+point lo 4 1024 368)/2 = (152908603:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152908603:ℝ)/42188800) = (13588480:ℝ)/11814337 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_367
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_022
