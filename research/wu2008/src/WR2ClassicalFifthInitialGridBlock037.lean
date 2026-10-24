import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints037
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_037 (j : Fin 16) : initialPayment (16*37+j.val) ≤
    initialValue ((point lo 4 1024 (16*37+j.val)+point lo 4 1024 (16*37+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 592 ≤ initialValue ((point lo 4 1024 592+point lo 4 1024 593)/2)
    have hp : initialPayment 592 = (293670460553:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 592+point lo 4 1024 593)/2 = (158339653:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158339653:ℝ)/42188800) = (13588480:ℝ)/10728127 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_592
  · change initialPayment 593 ≤ initialValue ((point lo 4 1024 593+point lo 4 1024 594)/2)
    have hp : initialPayment 593 = (294303650185:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 593+point lo 4 1024 594)/2 = (158363791:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158363791:ℝ)/42188800) = (67942400:ℝ)/53616497 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_593
  · change initialPayment 594 ≤ initialValue ((point lo 4 1024 594+point lo 4 1024 595)/2)
    have hp : initialPayment 594 = (294937384981:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 594+point lo 4 1024 595)/2 = (158387929:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158387929:ℝ)/42188800) = (67942400:ℝ)/53592359 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_594
  · change initialPayment 595 ≤ initialValue ((point lo 4 1024 595+point lo 4 1024 596)/2)
    have hp : initialPayment 595 = (295571665448:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 595+point lo 4 1024 596)/2 = (158412067:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158412067:ℝ)/42188800) = (67942400:ℝ)/53568221 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_595
  · change initialPayment 596 ≤ initialValue ((point lo 4 1024 596+point lo 4 1024 597)/2)
    have hp : initialPayment 596 = (296206492091:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 596+point lo 4 1024 597)/2 = (31687241:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31687241:ℝ)/8437760) = (67942400:ℝ)/53544083 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_596
  · change initialPayment 597 ≤ initialValue ((point lo 4 1024 597+point lo 4 1024 598)/2)
    have hp : initialPayment 597 = (296841865420:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 597+point lo 4 1024 598)/2 = (158460343:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158460343:ℝ)/42188800) = (13588480:ℝ)/10703989 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_597
  · change initialPayment 598 ≤ initialValue ((point lo 4 1024 598+point lo 4 1024 599)/2)
    have hp : initialPayment 598 = (297477785943:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 598+point lo 4 1024 599)/2 = (158484481:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158484481:ℝ)/42188800) = (67942400:ℝ)/53495807 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_598
  · change initialPayment 599 ≤ initialValue ((point lo 4 1024 599+point lo 4 1024 600)/2)
    have hp : initialPayment 599 = (298114254169:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 599+point lo 4 1024 600)/2 = (158508619:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158508619:ℝ)/42188800) = (67942400:ℝ)/53471669 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_599
  · change initialPayment 600 ≤ initialValue ((point lo 4 1024 600+point lo 4 1024 601)/2)
    have hp : initialPayment 600 = (298751270608:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 600+point lo 4 1024 601)/2 = (158532757:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158532757:ℝ)/42188800) = (67942400:ℝ)/53447531 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_600
  · change initialPayment 601 ≤ initialValue ((point lo 4 1024 601+point lo 4 1024 602)/2)
    have hp : initialPayment 601 = (299388835772:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 601+point lo 4 1024 602)/2 = (31711379:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31711379:ℝ)/8437760) = (67942400:ℝ)/53423393 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_601
  · change initialPayment 602 ≤ initialValue ((point lo 4 1024 602+point lo 4 1024 603)/2)
    have hp : initialPayment 602 = (300026950171:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 602+point lo 4 1024 603)/2 = (158581033:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158581033:ℝ)/42188800) = (13588480:ℝ)/10679851 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_602
  · change initialPayment 603 ≤ initialValue ((point lo 4 1024 603+point lo 4 1024 604)/2)
    have hp : initialPayment 603 = (300665614319:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 603+point lo 4 1024 604)/2 = (158605171:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158605171:ℝ)/42188800) = (67942400:ℝ)/53375117 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_603
  · change initialPayment 604 ≤ initialValue ((point lo 4 1024 604+point lo 4 1024 605)/2)
    have hp : initialPayment 604 = (301304828729:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 604+point lo 4 1024 605)/2 = (158629309:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158629309:ℝ)/42188800) = (67942400:ℝ)/53350979 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_604
  · change initialPayment 605 ≤ initialValue ((point lo 4 1024 605+point lo 4 1024 606)/2)
    have hp : initialPayment 605 = (301944593914:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 605+point lo 4 1024 606)/2 = (158653447:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158653447:ℝ)/42188800) = (67942400:ℝ)/53326841 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_605
  · change initialPayment 606 ≤ initialValue ((point lo 4 1024 606+point lo 4 1024 607)/2)
    have hp : initialPayment 606 = (302584910390:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 606+point lo 4 1024 607)/2 = (31735517:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31735517:ℝ)/8437760) = (67942400:ℝ)/53302703 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_606
  · change initialPayment 607 ≤ initialValue ((point lo 4 1024 607+point lo 4 1024 608)/2)
    have hp : initialPayment 607 = (303225778672:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 607+point lo 4 1024 608)/2 = (158701723:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158701723:ℝ)/42188800) = (13588480:ℝ)/10655713 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_607
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_037
