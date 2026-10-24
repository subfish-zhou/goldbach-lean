import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints034
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_034 (j : Fin 16) : initialPayment (16*34+j.val) ≤
    initialValue ((point lo 4 1024 (16*34+j.val)+point lo 4 1024 (16*34+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 544 ≤ initialValue ((point lo 4 1024 544+point lo 4 1024 545)/2)
    have hp : initialPayment 544 = (263908731898:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 544+point lo 4 1024 545)/2 = (157181029:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157181029:ℝ)/42188800) = (67942400:ℝ)/54799259 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_544
  · change initialPayment 545 ≤ initialValue ((point lo 4 1024 545+point lo 4 1024 546)/2)
    have hp : initialPayment 545 = (264516334632:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 545+point lo 4 1024 546)/2 = (157205167:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157205167:ℝ)/42188800) = (67942400:ℝ)/54775121 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_545
  · change initialPayment 546 ≤ initialValue ((point lo 4 1024 546+point lo 4 1024 547)/2)
    have hp : initialPayment 546 = (265124459091:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 546+point lo 4 1024 547)/2 = (31445861:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31445861:ℝ)/8437760) = (67942400:ℝ)/54750983 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_546
  · change initialPayment 547 ≤ initialValue ((point lo 4 1024 547+point lo 4 1024 548)/2)
    have hp : initialPayment 547 = (265733105745:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 547+point lo 4 1024 548)/2 = (157253443:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157253443:ℝ)/42188800) = (13588480:ℝ)/10945369 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_547
  · change initialPayment 548 ≤ initialValue ((point lo 4 1024 548+point lo 4 1024 549)/2)
    have hp : initialPayment 548 = (266342275066:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 548+point lo 4 1024 549)/2 = (157277581:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157277581:ℝ)/42188800) = (67942400:ℝ)/54702707 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_548
  · change initialPayment 549 ≤ initialValue ((point lo 4 1024 549+point lo 4 1024 550)/2)
    have hp : initialPayment 549 = (266951967529:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 549+point lo 4 1024 550)/2 = (157301719:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157301719:ℝ)/42188800) = (67942400:ℝ)/54678569 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_549
  · change initialPayment 550 ≤ initialValue ((point lo 4 1024 550+point lo 4 1024 551)/2)
    have hp : initialPayment 550 = (267562183605:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 550+point lo 4 1024 551)/2 = (157325857:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157325857:ℝ)/42188800) = (67942400:ℝ)/54654431 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_550
  · change initialPayment 551 ≤ initialValue ((point lo 4 1024 551+point lo 4 1024 552)/2)
    have hp : initialPayment 551 = (268172923770:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 551+point lo 4 1024 552)/2 = (31469999:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31469999:ℝ)/8437760) = (67942400:ℝ)/54630293 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_551
  · change initialPayment 552 ≤ initialValue ((point lo 4 1024 552+point lo 4 1024 553)/2)
    have hp : initialPayment 552 = (268784188499:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 552+point lo 4 1024 553)/2 = (157374133:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157374133:ℝ)/42188800) = (13588480:ℝ)/10921231 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_552
  · change initialPayment 553 ≤ initialValue ((point lo 4 1024 553+point lo 4 1024 554)/2)
    have hp : initialPayment 553 = (269395978266:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 553+point lo 4 1024 554)/2 = (157398271:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157398271:ℝ)/42188800) = (67942400:ℝ)/54582017 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_553
  · change initialPayment 554 ≤ initialValue ((point lo 4 1024 554+point lo 4 1024 555)/2)
    have hp : initialPayment 554 = (270008293549:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 554+point lo 4 1024 555)/2 = (157422409:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157422409:ℝ)/42188800) = (67942400:ℝ)/54557879 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_554
  · change initialPayment 555 ≤ initialValue ((point lo 4 1024 555+point lo 4 1024 556)/2)
    have hp : initialPayment 555 = (270621134825:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 555+point lo 4 1024 556)/2 = (157446547:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157446547:ℝ)/42188800) = (67942400:ℝ)/54533741 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_555
  · change initialPayment 556 ≤ initialValue ((point lo 4 1024 556+point lo 4 1024 557)/2)
    have hp : initialPayment 556 = (271234502571:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 556+point lo 4 1024 557)/2 = (31494137:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31494137:ℝ)/8437760) = (67942400:ℝ)/54509603 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_556
  · change initialPayment 557 ≤ initialValue ((point lo 4 1024 557+point lo 4 1024 558)/2)
    have hp : initialPayment 557 = (271848397266:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 557+point lo 4 1024 558)/2 = (157494823:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157494823:ℝ)/42188800) = (13588480:ℝ)/10897093 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_557
  · change initialPayment 558 ≤ initialValue ((point lo 4 1024 558+point lo 4 1024 559)/2)
    have hp : initialPayment 558 = (272462819389:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 558+point lo 4 1024 559)/2 = (157518961:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157518961:ℝ)/42188800) = (67942400:ℝ)/54461327 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_558
  · change initialPayment 559 ≤ initialValue ((point lo 4 1024 559+point lo 4 1024 560)/2)
    have hp : initialPayment 559 = (273077769420:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 559+point lo 4 1024 560)/2 = (157543099:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157543099:ℝ)/42188800) = (67942400:ℝ)/54437189 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_559
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_034
