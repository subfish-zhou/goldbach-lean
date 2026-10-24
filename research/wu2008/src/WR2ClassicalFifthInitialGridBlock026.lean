import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints026
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_026 (j : Fin 16) : initialPayment (16*26+j.val) ≤
    initialValue ((point lo 4 1024 (16*26+j.val)+point lo 4 1024 (16*26+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 416 ≤ initialValue ((point lo 4 1024 416+point lo 4 1024 417)/2)
    have hp : initialPayment 416 = (190282118439:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 416+point lo 4 1024 417)/2 = (30818273:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30818273:ℝ)/8437760) = (67942400:ℝ)/57888923 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_416
  · change initialPayment 417 ≤ initialValue ((point lo 4 1024 417+point lo 4 1024 418)/2)
    have hp : initialPayment 417 = (190826595437:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 417+point lo 4 1024 418)/2 = (154115503:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154115503:ℝ)/42188800) = (13588480:ℝ)/11572957 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_417
  · change initialPayment 418 ≤ initialValue ((point lo 4 1024 418+point lo 4 1024 419)/2)
    have hp : initialPayment 418 = (191371539203:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 418+point lo 4 1024 419)/2 = (154139641:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154139641:ℝ)/42188800) = (67942400:ℝ)/57840647 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_418
  · change initialPayment 419 ≤ initialValue ((point lo 4 1024 419+point lo 4 1024 420)/2)
    have hp : initialPayment 419 = (191916950127:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 419+point lo 4 1024 420)/2 = (154163779:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154163779:ℝ)/42188800) = (67942400:ℝ)/57816509 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_419
  · change initialPayment 420 ≤ initialValue ((point lo 4 1024 420+point lo 4 1024 421)/2)
    have hp : initialPayment 420 = (192462828601:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 420+point lo 4 1024 421)/2 = (154187917:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154187917:ℝ)/42188800) = (67942400:ℝ)/57792371 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_420
  · change initialPayment 421 ≤ initialValue ((point lo 4 1024 421+point lo 4 1024 422)/2)
    have hp : initialPayment 421 = (193009175016:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 421+point lo 4 1024 422)/2 = (30842411:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30842411:ℝ)/8437760) = (67942400:ℝ)/57768233 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_421
  · change initialPayment 422 ≤ initialValue ((point lo 4 1024 422+point lo 4 1024 423)/2)
    have hp : initialPayment 422 = (193555989764:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 422+point lo 4 1024 423)/2 = (154236193:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154236193:ℝ)/42188800) = (13588480:ℝ)/11548819 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_422
  · change initialPayment 423 ≤ initialValue ((point lo 4 1024 423+point lo 4 1024 424)/2)
    have hp : initialPayment 423 = (194103273239:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 423+point lo 4 1024 424)/2 = (154260331:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154260331:ℝ)/42188800) = (67942400:ℝ)/57719957 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_423
  · change initialPayment 424 ≤ initialValue ((point lo 4 1024 424+point lo 4 1024 425)/2)
    have hp : initialPayment 424 = (194651025834:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 424+point lo 4 1024 425)/2 = (154284469:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154284469:ℝ)/42188800) = (67942400:ℝ)/57695819 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_424
  · change initialPayment 425 ≤ initialValue ((point lo 4 1024 425+point lo 4 1024 426)/2)
    have hp : initialPayment 425 = (195199247943:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 425+point lo 4 1024 426)/2 = (154308607:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154308607:ℝ)/42188800) = (67942400:ℝ)/57671681 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_425
  · change initialPayment 426 ≤ initialValue ((point lo 4 1024 426+point lo 4 1024 427)/2)
    have hp : initialPayment 426 = (195747939960:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 426+point lo 4 1024 427)/2 = (30866549:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30866549:ℝ)/8437760) = (67942400:ℝ)/57647543 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_426
  · change initialPayment 427 ≤ initialValue ((point lo 4 1024 427+point lo 4 1024 428)/2)
    have hp : initialPayment 427 = (196297102280:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 427+point lo 4 1024 428)/2 = (154356883:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154356883:ℝ)/42188800) = (13588480:ℝ)/11524681 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_427
  · change initialPayment 428 ≤ initialValue ((point lo 4 1024 428+point lo 4 1024 429)/2)
    have hp : initialPayment 428 = (196846735301:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 428+point lo 4 1024 429)/2 = (154381021:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154381021:ℝ)/42188800) = (67942400:ℝ)/57599267 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_428
  · change initialPayment 429 ≤ initialValue ((point lo 4 1024 429+point lo 4 1024 430)/2)
    have hp : initialPayment 429 = (197396839416:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 429+point lo 4 1024 430)/2 = (154405159:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154405159:ℝ)/42188800) = (67942400:ℝ)/57575129 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_429
  · change initialPayment 430 ≤ initialValue ((point lo 4 1024 430+point lo 4 1024 431)/2)
    have hp : initialPayment 430 = (197947415025:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 430+point lo 4 1024 431)/2 = (154429297:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154429297:ℝ)/42188800) = (67942400:ℝ)/57550991 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_430
  · change initialPayment 431 ≤ initialValue ((point lo 4 1024 431+point lo 4 1024 432)/2)
    have hp : initialPayment 431 = (198498462523:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 431+point lo 4 1024 432)/2 = (30890687:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30890687:ℝ)/8437760) = (67942400:ℝ)/57526853 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_431
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_026
