import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints024
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_024 (j : Fin 16) : initialPayment (16*24+j.val) ≤
    initialValue ((point lo 4 1024 (16*24+j.val)+point lo 4 1024 (16*24+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 384 ≤ initialValue ((point lo 4 1024 384+point lo 4 1024 385)/2)
    have hp : initialPayment 384 = (173103000419:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 384+point lo 4 1024 385)/2 = (153318949:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153318949:ℝ)/42188800) = (67942400:ℝ)/58661339 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_384
  · change initialPayment 385 ≤ initialValue ((point lo 4 1024 385+point lo 4 1024 386)/2)
    have hp : initialPayment 385 = (173632743686:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 385+point lo 4 1024 386)/2 = (153343087:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153343087:ℝ)/42188800) = (67942400:ℝ)/58637201 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_385
  · change initialPayment 386 ≤ initialValue ((point lo 4 1024 386+point lo 4 1024 387)/2)
    have hp : initialPayment 386 = (174162941520:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 386+point lo 4 1024 387)/2 = (6134689:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6134689:ℝ)/1687552) = (67942400:ℝ)/58613063 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_386
  · change initialPayment 387 ≤ initialValue ((point lo 4 1024 387+point lo 4 1024 388)/2)
    have hp : initialPayment 387 = (174693594293:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 387+point lo 4 1024 388)/2 = (153391363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153391363:ℝ)/42188800) = (2717696:ℝ)/2343557 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_387
  · change initialPayment 388 ≤ initialValue ((point lo 4 1024 388+point lo 4 1024 389)/2)
    have hp : initialPayment 388 = (175224702379:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 388+point lo 4 1024 389)/2 = (153415501:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153415501:ℝ)/42188800) = (67942400:ℝ)/58564787 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_388
  · change initialPayment 389 ≤ initialValue ((point lo 4 1024 389+point lo 4 1024 390)/2)
    have hp : initialPayment 389 = (175756266151:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 389+point lo 4 1024 390)/2 = (153439639:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153439639:ℝ)/42188800) = (67942400:ℝ)/58540649 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_389
  · change initialPayment 390 ≤ initialValue ((point lo 4 1024 390+point lo 4 1024 391)/2)
    have hp : initialPayment 390 = (176288285984:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 390+point lo 4 1024 391)/2 = (153463777:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153463777:ℝ)/42188800) = (67942400:ℝ)/58516511 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_390
  · change initialPayment 391 ≤ initialValue ((point lo 4 1024 391+point lo 4 1024 392)/2)
    have hp : initialPayment 391 = (176820762252:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 391+point lo 4 1024 392)/2 = (30697583:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30697583:ℝ)/8437760) = (67942400:ℝ)/58492373 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_391
  · change initialPayment 392 ≤ initialValue ((point lo 4 1024 392+point lo 4 1024 393)/2)
    have hp : initialPayment 392 = (177353695332:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 392+point lo 4 1024 393)/2 = (153512053:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153512053:ℝ)/42188800) = (13588480:ℝ)/11693647 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_392
  · change initialPayment 393 ≤ initialValue ((point lo 4 1024 393+point lo 4 1024 394)/2)
    have hp : initialPayment 393 = (177887085599:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 393+point lo 4 1024 394)/2 = (153536191:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153536191:ℝ)/42188800) = (67942400:ℝ)/58444097 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_393
  · change initialPayment 394 ≤ initialValue ((point lo 4 1024 394+point lo 4 1024 395)/2)
    have hp : initialPayment 394 = (178420933429:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 394+point lo 4 1024 395)/2 = (153560329:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153560329:ℝ)/42188800) = (67942400:ℝ)/58419959 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_394
  · change initialPayment 395 ≤ initialValue ((point lo 4 1024 395+point lo 4 1024 396)/2)
    have hp : initialPayment 395 = (178955239201:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 395+point lo 4 1024 396)/2 = (153584467:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153584467:ℝ)/42188800) = (67942400:ℝ)/58395821 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_395
  · change initialPayment 396 ≤ initialValue ((point lo 4 1024 396+point lo 4 1024 397)/2)
    have hp : initialPayment 396 = (179490003290:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 396+point lo 4 1024 397)/2 = (30721721:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30721721:ℝ)/8437760) = (67942400:ℝ)/58371683 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_396
  · change initialPayment 397 ≤ initialValue ((point lo 4 1024 397+point lo 4 1024 398)/2)
    have hp : initialPayment 397 = (180025226076:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 397+point lo 4 1024 398)/2 = (153632743:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153632743:ℝ)/42188800) = (13588480:ℝ)/11669509 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_397
  · change initialPayment 398 ≤ initialValue ((point lo 4 1024 398+point lo 4 1024 399)/2)
    have hp : initialPayment 398 = (180560907938:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 398+point lo 4 1024 399)/2 = (153656881:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153656881:ℝ)/42188800) = (67942400:ℝ)/58323407 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_398
  · change initialPayment 399 ≤ initialValue ((point lo 4 1024 399+point lo 4 1024 400)/2)
    have hp : initialPayment 399 = (181097049254:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 399+point lo 4 1024 400)/2 = (153681019:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153681019:ℝ)/42188800) = (67942400:ℝ)/58299269 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_399
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_024
