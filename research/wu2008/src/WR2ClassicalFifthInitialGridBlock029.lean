import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints029
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_029 (j : Fin 16) : initialPayment (16*29+j.val) ≤
    initialValue ((point lo 4 1024 (16*29+j.val)+point lo 4 1024 (16*29+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 464 ≤ initialValue ((point lo 4 1024 464+point lo 4 1024 465)/2)
    have hp : initialPayment 464 = (216950396446:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 464+point lo 4 1024 465)/2 = (155249989:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155249989:ℝ)/42188800) = (67942400:ℝ)/56730299 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_464
  · change initialPayment 465 ≤ initialValue ((point lo 4 1024 465+point lo 4 1024 466)/2)
    have hp : initialPayment 465 = (217517728919:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 465+point lo 4 1024 466)/2 = (155274127:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155274127:ℝ)/42188800) = (67942400:ℝ)/56706161 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_465
  · change initialPayment 466 ≤ initialValue ((point lo 4 1024 466+point lo 4 1024 467)/2)
    have hp : initialPayment 466 = (218085547567:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 466+point lo 4 1024 467)/2 = (31059653:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31059653:ℝ)/8437760) = (67942400:ℝ)/56682023 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_466
  · change initialPayment 467 ≤ initialValue ((point lo 4 1024 467+point lo 4 1024 468)/2)
    have hp : initialPayment 467 = (218653852810:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 467+point lo 4 1024 468)/2 = (155322403:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155322403:ℝ)/42188800) = (13588480:ℝ)/11331577 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_467
  · change initialPayment 468 ≤ initialValue ((point lo 4 1024 468+point lo 4 1024 469)/2)
    have hp : initialPayment 468 = (219222645066:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 468+point lo 4 1024 469)/2 = (155346541:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155346541:ℝ)/42188800) = (67942400:ℝ)/56633747 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_468
  · change initialPayment 469 ≤ initialValue ((point lo 4 1024 469+point lo 4 1024 470)/2)
    have hp : initialPayment 469 = (219791924756:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 469+point lo 4 1024 470)/2 = (155370679:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155370679:ℝ)/42188800) = (67942400:ℝ)/56609609 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_469
  · change initialPayment 470 ≤ initialValue ((point lo 4 1024 470+point lo 4 1024 471)/2)
    have hp : initialPayment 470 = (220361692302:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 470+point lo 4 1024 471)/2 = (155394817:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155394817:ℝ)/42188800) = (67942400:ℝ)/56585471 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_470
  · change initialPayment 471 ≤ initialValue ((point lo 4 1024 471+point lo 4 1024 472)/2)
    have hp : initialPayment 471 = (220931948124:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 471+point lo 4 1024 472)/2 = (31083791:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31083791:ℝ)/8437760) = (67942400:ℝ)/56561333 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_471
  · change initialPayment 472 ≤ initialValue ((point lo 4 1024 472+point lo 4 1024 473)/2)
    have hp : initialPayment 472 = (221502692644:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 472+point lo 4 1024 473)/2 = (155443093:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155443093:ℝ)/42188800) = (13588480:ℝ)/11307439 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_472
  · change initialPayment 473 ≤ initialValue ((point lo 4 1024 473+point lo 4 1024 474)/2)
    have hp : initialPayment 473 = (222073926286:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 473+point lo 4 1024 474)/2 = (155467231:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155467231:ℝ)/42188800) = (67942400:ℝ)/56513057 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_473
  · change initialPayment 474 ≤ initialValue ((point lo 4 1024 474+point lo 4 1024 475)/2)
    have hp : initialPayment 474 = (222645649473:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 474+point lo 4 1024 475)/2 = (155491369:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155491369:ℝ)/42188800) = (67942400:ℝ)/56488919 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_474
  · change initialPayment 475 ≤ initialValue ((point lo 4 1024 475+point lo 4 1024 476)/2)
    have hp : initialPayment 475 = (223217862628:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 475+point lo 4 1024 476)/2 = (155515507:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155515507:ℝ)/42188800) = (67942400:ℝ)/56464781 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_475
  · change initialPayment 476 ≤ initialValue ((point lo 4 1024 476+point lo 4 1024 477)/2)
    have hp : initialPayment 476 = (223790566176:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 476+point lo 4 1024 477)/2 = (31107929:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31107929:ℝ)/8437760) = (67942400:ℝ)/56440643 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_476
  · change initialPayment 477 ≤ initialValue ((point lo 4 1024 477+point lo 4 1024 478)/2)
    have hp : initialPayment 477 = (224363760543:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 477+point lo 4 1024 478)/2 = (155563783:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155563783:ℝ)/42188800) = (13588480:ℝ)/11283301 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_477
  · change initialPayment 478 ≤ initialValue ((point lo 4 1024 478+point lo 4 1024 479)/2)
    have hp : initialPayment 478 = (224937446155:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 478+point lo 4 1024 479)/2 = (155587921:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155587921:ℝ)/42188800) = (67942400:ℝ)/56392367 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_478
  · change initialPayment 479 ≤ initialValue ((point lo 4 1024 479+point lo 4 1024 480)/2)
    have hp : initialPayment 479 = (225511623437:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 479+point lo 4 1024 480)/2 = (155612059:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155612059:ℝ)/42188800) = (67942400:ℝ)/56368229 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_479
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_029
