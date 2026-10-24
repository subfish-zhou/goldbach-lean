import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints028
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_028 (j : Fin 16) : initialPayment (16*28+j.val) ≤
    initialValue ((point lo 4 1024 (16*28+j.val)+point lo 4 1024 (16*28+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 448 ≤ initialValue ((point lo 4 1024 448+point lo 4 1024 449)/2)
    have hp : initialPayment 448 = (207938857167:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 448+point lo 4 1024 449)/2 = (154863781:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154863781:ℝ)/42188800) = (67942400:ℝ)/57116507 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_448
  · change initialPayment 449 ≤ initialValue ((point lo 4 1024 449+point lo 4 1024 450)/2)
    have hp : initialPayment 449 = (208498467324:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 449+point lo 4 1024 450)/2 = (154887919:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154887919:ℝ)/42188800) = (67942400:ℝ)/57092369 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_449
  · change initialPayment 450 ≤ initialValue ((point lo 4 1024 450+point lo 4 1024 451)/2)
    have hp : initialPayment 450 = (209058557034:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 450+point lo 4 1024 451)/2 = (154912057:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154912057:ℝ)/42188800) = (67942400:ℝ)/57068231 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_450
  · change initialPayment 451 ≤ initialValue ((point lo 4 1024 451+point lo 4 1024 452)/2)
    have hp : initialPayment 451 = (209619126708:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 451+point lo 4 1024 452)/2 = (30987239:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30987239:ℝ)/8437760) = (67942400:ℝ)/57044093 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_451
  · change initialPayment 452 ≤ initialValue ((point lo 4 1024 452+point lo 4 1024 453)/2)
    have hp : initialPayment 452 = (210180176755:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 452+point lo 4 1024 453)/2 = (154960333:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154960333:ℝ)/42188800) = (13588480:ℝ)/11403991 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_452
  · change initialPayment 453 ≤ initialValue ((point lo 4 1024 453+point lo 4 1024 454)/2)
    have hp : initialPayment 453 = (210741707586:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 453+point lo 4 1024 454)/2 = (154984471:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154984471:ℝ)/42188800) = (67942400:ℝ)/56995817 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_453
  · change initialPayment 454 ≤ initialValue ((point lo 4 1024 454+point lo 4 1024 455)/2)
    have hp : initialPayment 454 = (211303719611:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 454+point lo 4 1024 455)/2 = (155008609:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155008609:ℝ)/42188800) = (67942400:ℝ)/56971679 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_454
  · change initialPayment 455 ≤ initialValue ((point lo 4 1024 455+point lo 4 1024 456)/2)
    have hp : initialPayment 455 = (211866213243:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 455+point lo 4 1024 456)/2 = (155032747:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155032747:ℝ)/42188800) = (67942400:ℝ)/56947541 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_455
  · change initialPayment 456 ≤ initialValue ((point lo 4 1024 456+point lo 4 1024 457)/2)
    have hp : initialPayment 456 = (212429188893:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 456+point lo 4 1024 457)/2 = (31011377:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31011377:ℝ)/8437760) = (67942400:ℝ)/56923403 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_456
  · change initialPayment 457 ≤ initialValue ((point lo 4 1024 457+point lo 4 1024 458)/2)
    have hp : initialPayment 457 = (212992646975:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 457+point lo 4 1024 458)/2 = (1505641:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((1505641:ℝ)/409600) = (13588480:ℝ)/11379853 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_457
  · change initialPayment 458 ≤ initialValue ((point lo 4 1024 458+point lo 4 1024 459)/2)
    have hp : initialPayment 458 = (213556587902:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 458+point lo 4 1024 459)/2 = (155105161:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155105161:ℝ)/42188800) = (67942400:ℝ)/56875127 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_458
  · change initialPayment 459 ≤ initialValue ((point lo 4 1024 459+point lo 4 1024 460)/2)
    have hp : initialPayment 459 = (214121012088:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 459+point lo 4 1024 460)/2 = (155129299:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155129299:ℝ)/42188800) = (67942400:ℝ)/56850989 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_459
  · change initialPayment 460 ≤ initialValue ((point lo 4 1024 460+point lo 4 1024 461)/2)
    have hp : initialPayment 460 = (214685919949:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 460+point lo 4 1024 461)/2 = (155153437:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155153437:ℝ)/42188800) = (67942400:ℝ)/56826851 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_460
  · change initialPayment 461 ≤ initialValue ((point lo 4 1024 461+point lo 4 1024 462)/2)
    have hp : initialPayment 461 = (215251311898:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 461+point lo 4 1024 462)/2 = (6207103:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6207103:ℝ)/1687552) = (67942400:ℝ)/56802713 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_461
  · change initialPayment 462 ≤ initialValue ((point lo 4 1024 462+point lo 4 1024 463)/2)
    have hp : initialPayment 462 = (215817188353:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 462+point lo 4 1024 463)/2 = (155201713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155201713:ℝ)/42188800) = (2717696:ℝ)/2271143 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_462
  · change initialPayment 463 ≤ initialValue ((point lo 4 1024 463+point lo 4 1024 464)/2)
    have hp : initialPayment 463 = (216383549730:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 463+point lo 4 1024 464)/2 = (155225851:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((155225851:ℝ)/42188800) = (67942400:ℝ)/56754437 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_463
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_028
