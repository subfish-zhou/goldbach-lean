import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints017
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_017 (j : Fin 16) : initialPayment (16*17+j.val) ≤
    initialValue ((point lo 4 1024 (16*17+j.val)+point lo 4 1024 (16*17+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 272 ≤ initialValue ((point lo 4 1024 272+point lo 4 1024 273)/2)
    have hp : initialPayment 272 = (116562270905:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 272+point lo 4 1024 273)/2 = (150615493:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150615493:ℝ)/42188800) = (13588480:ℝ)/12272959 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_272
  · change initialPayment 273 ≤ initialValue ((point lo 4 1024 273+point lo 4 1024 274)/2)
    have hp : initialPayment 273 = (117043335525:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 273+point lo 4 1024 274)/2 = (150639631:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150639631:ℝ)/42188800) = (67942400:ℝ)/61340657 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_273
  · change initialPayment 274 ≤ initialValue ((point lo 4 1024 274+point lo 4 1024 275)/2)
    have hp : initialPayment 274 = (117524816233:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 274+point lo 4 1024 275)/2 = (150663769:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150663769:ℝ)/42188800) = (67942400:ℝ)/61316519 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_274
  · change initialPayment 275 ≤ initialValue ((point lo 4 1024 275+point lo 4 1024 276)/2)
    have hp : initialPayment 275 = (118006713345:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 275+point lo 4 1024 276)/2 = (150687907:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150687907:ℝ)/42188800) = (67942400:ℝ)/61292381 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_275
  · change initialPayment 276 ≤ initialValue ((point lo 4 1024 276+point lo 4 1024 277)/2)
    have hp : initialPayment 276 = (118489027179:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 276+point lo 4 1024 277)/2 = (30142409:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30142409:ℝ)/8437760) = (67942400:ℝ)/61268243 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_276
  · change initialPayment 277 ≤ initialValue ((point lo 4 1024 277+point lo 4 1024 278)/2)
    have hp : initialPayment 277 = (118971758051:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 277+point lo 4 1024 278)/2 = (150736183:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150736183:ℝ)/42188800) = (13588480:ℝ)/12248821 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_277
  · change initialPayment 278 ≤ initialValue ((point lo 4 1024 278+point lo 4 1024 279)/2)
    have hp : initialPayment 278 = (119454906279:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 278+point lo 4 1024 279)/2 = (150760321:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150760321:ℝ)/42188800) = (67942400:ℝ)/61219967 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_278
  · change initialPayment 279 ≤ initialValue ((point lo 4 1024 279+point lo 4 1024 280)/2)
    have hp : initialPayment 279 = (119938472182:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 279+point lo 4 1024 280)/2 = (150784459:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150784459:ℝ)/42188800) = (67942400:ℝ)/61195829 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_279
  · change initialPayment 280 ≤ initialValue ((point lo 4 1024 280+point lo 4 1024 281)/2)
    have hp : initialPayment 280 = (120422456079:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 280+point lo 4 1024 281)/2 = (150808597:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150808597:ℝ)/42188800) = (67942400:ℝ)/61171691 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_280
  · change initialPayment 281 ≤ initialValue ((point lo 4 1024 281+point lo 4 1024 282)/2)
    have hp : initialPayment 281 = (120906858288:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 281+point lo 4 1024 282)/2 = (30166547:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30166547:ℝ)/8437760) = (67942400:ℝ)/61147553 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_281
  · change initialPayment 282 ≤ initialValue ((point lo 4 1024 282+point lo 4 1024 283)/2)
    have hp : initialPayment 282 = (121391679130:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 282+point lo 4 1024 283)/2 = (150856873:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150856873:ℝ)/42188800) = (13588480:ℝ)/12224683 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_282
  · change initialPayment 283 ≤ initialValue ((point lo 4 1024 283+point lo 4 1024 284)/2)
    have hp : initialPayment 283 = (121876918924:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 283+point lo 4 1024 284)/2 = (150881011:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150881011:ℝ)/42188800) = (67942400:ℝ)/61099277 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_283
  · change initialPayment 284 ≤ initialValue ((point lo 4 1024 284+point lo 4 1024 285)/2)
    have hp : initialPayment 284 = (122362577991:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 284+point lo 4 1024 285)/2 = (150905149:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150905149:ℝ)/42188800) = (67942400:ℝ)/61075139 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_284
  · change initialPayment 285 ≤ initialValue ((point lo 4 1024 285+point lo 4 1024 286)/2)
    have hp : initialPayment 285 = (122848656652:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 285+point lo 4 1024 286)/2 = (150929287:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150929287:ℝ)/42188800) = (67942400:ℝ)/61051001 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_285
  · change initialPayment 286 ≤ initialValue ((point lo 4 1024 286+point lo 4 1024 287)/2)
    have hp : initialPayment 286 = (123335155229:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 286+point lo 4 1024 287)/2 = (6038137:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6038137:ℝ)/1687552) = (67942400:ℝ)/61026863 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_286
  · change initialPayment 287 ≤ initialValue ((point lo 4 1024 287+point lo 4 1024 288)/2)
    have hp : initialPayment 287 = (123822074043:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 287+point lo 4 1024 288)/2 = (150977563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150977563:ℝ)/42188800) = (2717696:ℝ)/2440109 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_287
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_017
