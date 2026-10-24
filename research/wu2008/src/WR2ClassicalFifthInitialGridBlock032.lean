import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints032
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_032 (j : Fin 16) : initialPayment (16*32+j.val) ≤
    initialValue ((point lo 4 1024 (16*32+j.val)+point lo 4 1024 (16*32+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 512 ≤ initialValue ((point lo 4 1024 512+point lo 4 1024 513)/2)
    have hp : initialPayment 512 = (244738129620:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 512+point lo 4 1024 513)/2 = (156408613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156408613:ℝ)/42188800) = (2717696:ℝ)/2222867 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_512
  · change initialPayment 513 ≤ initialValue ((point lo 4 1024 513+point lo 4 1024 514)/2)
    have hp : initialPayment 513 = (245329281995:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 513+point lo 4 1024 514)/2 = (156432751:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156432751:ℝ)/42188800) = (67942400:ℝ)/55547537 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_513
  · change initialPayment 514 ≤ initialValue ((point lo 4 1024 514+point lo 4 1024 515)/2)
    have hp : initialPayment 514 = (245920941370:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 514+point lo 4 1024 515)/2 = (156456889:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156456889:ℝ)/42188800) = (67942400:ℝ)/55523399 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_514
  · change initialPayment 515 ≤ initialValue ((point lo 4 1024 515+point lo 4 1024 516)/2)
    have hp : initialPayment 515 = (246513108194:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 515+point lo 4 1024 516)/2 = (156481027:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156481027:ℝ)/42188800) = (67942400:ℝ)/55499261 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_515
  · change initialPayment 516 ≤ initialValue ((point lo 4 1024 516+point lo 4 1024 517)/2)
    have hp : initialPayment 516 = (247105782917:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 516+point lo 4 1024 517)/2 = (31301033:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31301033:ℝ)/8437760) = (67942400:ℝ)/55475123 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_516
  · change initialPayment 517 ≤ initialValue ((point lo 4 1024 517+point lo 4 1024 518)/2)
    have hp : initialPayment 517 = (247698965991:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 517+point lo 4 1024 518)/2 = (156529303:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156529303:ℝ)/42188800) = (13588480:ℝ)/11090197 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_517
  · change initialPayment 518 ≤ initialValue ((point lo 4 1024 518+point lo 4 1024 519)/2)
    have hp : initialPayment 518 = (248292657867:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 518+point lo 4 1024 519)/2 = (156553441:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156553441:ℝ)/42188800) = (67942400:ℝ)/55426847 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_518
  · change initialPayment 519 ≤ initialValue ((point lo 4 1024 519+point lo 4 1024 520)/2)
    have hp : initialPayment 519 = (248886858997:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 519+point lo 4 1024 520)/2 = (156577579:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156577579:ℝ)/42188800) = (67942400:ℝ)/55402709 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_519
  · change initialPayment 520 ≤ initialValue ((point lo 4 1024 520+point lo 4 1024 521)/2)
    have hp : initialPayment 520 = (249481569835:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 520+point lo 4 1024 521)/2 = (156601717:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156601717:ℝ)/42188800) = (67942400:ℝ)/55378571 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_520
  · change initialPayment 521 ≤ initialValue ((point lo 4 1024 521+point lo 4 1024 522)/2)
    have hp : initialPayment 521 = (250076790835:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 521+point lo 4 1024 522)/2 = (31325171:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31325171:ℝ)/8437760) = (67942400:ℝ)/55354433 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_521
  · change initialPayment 522 ≤ initialValue ((point lo 4 1024 522+point lo 4 1024 523)/2)
    have hp : initialPayment 522 = (250672522450:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 522+point lo 4 1024 523)/2 = (156649993:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156649993:ℝ)/42188800) = (13588480:ℝ)/11066059 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_522
  · change initialPayment 523 ≤ initialValue ((point lo 4 1024 523+point lo 4 1024 524)/2)
    have hp : initialPayment 523 = (251268765136:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 523+point lo 4 1024 524)/2 = (156674131:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156674131:ℝ)/42188800) = (67942400:ℝ)/55306157 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_523
  · change initialPayment 524 ≤ initialValue ((point lo 4 1024 524+point lo 4 1024 525)/2)
    have hp : initialPayment 524 = (251865519348:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 524+point lo 4 1024 525)/2 = (156698269:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156698269:ℝ)/42188800) = (67942400:ℝ)/55282019 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_524
  · change initialPayment 525 ≤ initialValue ((point lo 4 1024 525+point lo 4 1024 526)/2)
    have hp : initialPayment 525 = (252462785542:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 525+point lo 4 1024 526)/2 = (156722407:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156722407:ℝ)/42188800) = (67942400:ℝ)/55257881 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_525
  · change initialPayment 526 ≤ initialValue ((point lo 4 1024 526+point lo 4 1024 527)/2)
    have hp : initialPayment 526 = (253060564177:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 526+point lo 4 1024 527)/2 = (31349309:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31349309:ℝ)/8437760) = (67942400:ℝ)/55233743 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_526
  · change initialPayment 527 ≤ initialValue ((point lo 4 1024 527+point lo 4 1024 528)/2)
    have hp : initialPayment 527 = (253658855709:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 527+point lo 4 1024 528)/2 = (156770683:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156770683:ℝ)/42188800) = (13588480:ℝ)/11041921 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_527
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_032
