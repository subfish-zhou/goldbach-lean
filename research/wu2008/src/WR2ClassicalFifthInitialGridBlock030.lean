import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints030
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_030 (j : Fin 16) : initialPayment (16*30+j.val) ≤
    initialValue ((point lo 4 1024 (16*30+j.val)+point lo 4 1024 (16*30+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 480 ≤ initialValue ((point lo 4 1024 480+point lo 4 1024 481)/2)
    have hp : initialPayment 480 = (226086292817:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 480+point lo 4 1024 481)/2 = (155636197:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155636197:ℝ)/42188800) = (67942400:ℝ)/56344091 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_480
  · change initialPayment 481 ≤ initialValue ((point lo 4 1024 481+point lo 4 1024 482)/2)
    have hp : initialPayment 481 = (226661454722:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 481+point lo 4 1024 482)/2 = (31132067:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31132067:ℝ)/8437760) = (67942400:ℝ)/56319953 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_481
  · change initialPayment 482 ≤ initialValue ((point lo 4 1024 482+point lo 4 1024 483)/2)
    have hp : initialPayment 482 = (227237109582:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 482+point lo 4 1024 483)/2 = (155684473:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155684473:ℝ)/42188800) = (13588480:ℝ)/11259163 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_482
  · change initialPayment 483 ≤ initialValue ((point lo 4 1024 483+point lo 4 1024 484)/2)
    have hp : initialPayment 483 = (227813257824:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 483+point lo 4 1024 484)/2 = (155708611:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155708611:ℝ)/42188800) = (67942400:ℝ)/56271677 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_483
  · change initialPayment 484 ≤ initialValue ((point lo 4 1024 484+point lo 4 1024 485)/2)
    have hp : initialPayment 484 = (228389899880:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 484+point lo 4 1024 485)/2 = (155732749:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155732749:ℝ)/42188800) = (67942400:ℝ)/56247539 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_484
  · change initialPayment 485 ≤ initialValue ((point lo 4 1024 485+point lo 4 1024 486)/2)
    have hp : initialPayment 485 = (228967036177:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 485+point lo 4 1024 486)/2 = (155756887:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155756887:ℝ)/42188800) = (67942400:ℝ)/56223401 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_485
  · change initialPayment 486 ≤ initialValue ((point lo 4 1024 486+point lo 4 1024 487)/2)
    have hp : initialPayment 486 = (229544667149:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 486+point lo 4 1024 487)/2 = (6231241:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6231241:ℝ)/1687552) = (67942400:ℝ)/56199263 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_486
  · change initialPayment 487 ≤ initialValue ((point lo 4 1024 487+point lo 4 1024 488)/2)
    have hp : initialPayment 487 = (230122793226:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 487+point lo 4 1024 488)/2 = (155805163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155805163:ℝ)/42188800) = (2717696:ℝ)/2247005 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_487
  · change initialPayment 488 ≤ initialValue ((point lo 4 1024 488+point lo 4 1024 489)/2)
    have hp : initialPayment 488 = (230701414840:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 488+point lo 4 1024 489)/2 = (155829301:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155829301:ℝ)/42188800) = (67942400:ℝ)/56150987 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_488
  · change initialPayment 489 ≤ initialValue ((point lo 4 1024 489+point lo 4 1024 490)/2)
    have hp : initialPayment 489 = (231280532424:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 489+point lo 4 1024 490)/2 = (155853439:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155853439:ℝ)/42188800) = (67942400:ℝ)/56126849 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_489
  · change initialPayment 490 ≤ initialValue ((point lo 4 1024 490+point lo 4 1024 491)/2)
    have hp : initialPayment 490 = (231860146412:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 490+point lo 4 1024 491)/2 = (155877577:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155877577:ℝ)/42188800) = (67942400:ℝ)/56102711 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_490
  · change initialPayment 491 ≤ initialValue ((point lo 4 1024 491+point lo 4 1024 492)/2)
    have hp : initialPayment 491 = (232440257238:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 491+point lo 4 1024 492)/2 = (31180343:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31180343:ℝ)/8437760) = (67942400:ℝ)/56078573 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_491
  · change initialPayment 492 ≤ initialValue ((point lo 4 1024 492+point lo 4 1024 493)/2)
    have hp : initialPayment 492 = (233020865335:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 492+point lo 4 1024 493)/2 = (155925853:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155925853:ℝ)/42188800) = (13588480:ℝ)/11210887 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_492
  · change initialPayment 493 ≤ initialValue ((point lo 4 1024 493+point lo 4 1024 494)/2)
    have hp : initialPayment 493 = (233601971141:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 493+point lo 4 1024 494)/2 = (155949991:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155949991:ℝ)/42188800) = (67942400:ℝ)/56030297 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_493
  · change initialPayment 494 ≤ initialValue ((point lo 4 1024 494+point lo 4 1024 495)/2)
    have hp : initialPayment 494 = (234183575090:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 494+point lo 4 1024 495)/2 = (155974129:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155974129:ℝ)/42188800) = (67942400:ℝ)/56006159 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_494
  · change initialPayment 495 ≤ initialValue ((point lo 4 1024 495+point lo 4 1024 496)/2)
    have hp : initialPayment 495 = (234765677619:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 495+point lo 4 1024 496)/2 = (155998267:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155998267:ℝ)/42188800) = (67942400:ℝ)/55982021 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_495
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_030
