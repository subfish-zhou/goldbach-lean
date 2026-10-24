import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints038
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_038 (j : Fin 16) : initialPayment (16*38+j.val) ≤
    initialValue ((point lo 4 1024 (16*38+j.val)+point lo 4 1024 (16*38+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 608 ≤ initialValue ((point lo 4 1024 608+point lo 4 1024 609)/2)
    have hp : initialPayment 608 = (303867199277:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 608+point lo 4 1024 609)/2 = (158725861:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158725861:ℝ)/42188800) = (67942400:ℝ)/53254427 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_608
  · change initialPayment 609 ≤ initialValue ((point lo 4 1024 609+point lo 4 1024 610)/2)
    have hp : initialPayment 609 = (304509172720:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 609+point lo 4 1024 610)/2 = (158749999:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158749999:ℝ)/42188800) = (67942400:ℝ)/53230289 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_609
  · change initialPayment 610 ≤ initialValue ((point lo 4 1024 610+point lo 4 1024 611)/2)
    have hp : initialPayment 610 = (305151699521:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 610+point lo 4 1024 611)/2 = (158774137:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158774137:ℝ)/42188800) = (67942400:ℝ)/53206151 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_610
  · change initialPayment 611 ≤ initialValue ((point lo 4 1024 611+point lo 4 1024 612)/2)
    have hp : initialPayment 611 = (305794780198:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 611+point lo 4 1024 612)/2 = (6351931:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6351931:ℝ)/1687552) = (67942400:ℝ)/53182013 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_611
  · change initialPayment 612 ≤ initialValue ((point lo 4 1024 612+point lo 4 1024 613)/2)
    have hp : initialPayment 612 = (306438415270:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 612+point lo 4 1024 613)/2 = (158822413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158822413:ℝ)/42188800) = (2717696:ℝ)/2126315 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_612
  · change initialPayment 613 ≤ initialValue ((point lo 4 1024 613+point lo 4 1024 614)/2)
    have hp : initialPayment 613 = (307082605258:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 613+point lo 4 1024 614)/2 = (158846551:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158846551:ℝ)/42188800) = (67942400:ℝ)/53133737 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_613
  · change initialPayment 614 ≤ initialValue ((point lo 4 1024 614+point lo 4 1024 615)/2)
    have hp : initialPayment 614 = (307727350682:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 614+point lo 4 1024 615)/2 = (158870689:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158870689:ℝ)/42188800) = (67942400:ℝ)/53109599 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_614
  · change initialPayment 615 ≤ initialValue ((point lo 4 1024 615+point lo 4 1024 616)/2)
    have hp : initialPayment 615 = (308372652065:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 615+point lo 4 1024 616)/2 = (158894827:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158894827:ℝ)/42188800) = (67942400:ℝ)/53085461 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_615
  · change initialPayment 616 ≤ initialValue ((point lo 4 1024 616+point lo 4 1024 617)/2)
    have hp : initialPayment 616 = (309018509928:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 616+point lo 4 1024 617)/2 = (31783793:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31783793:ℝ)/8437760) = (67942400:ℝ)/53061323 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_616
  · change initialPayment 617 ≤ initialValue ((point lo 4 1024 617+point lo 4 1024 618)/2)
    have hp : initialPayment 617 = (309664924796:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 617+point lo 4 1024 618)/2 = (158943103:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158943103:ℝ)/42188800) = (13588480:ℝ)/10607437 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_617
  · change initialPayment 618 ≤ initialValue ((point lo 4 1024 618+point lo 4 1024 619)/2)
    have hp : initialPayment 618 = (310311897191:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 618+point lo 4 1024 619)/2 = (158967241:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158967241:ℝ)/42188800) = (67942400:ℝ)/53013047 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_618
  · change initialPayment 619 ≤ initialValue ((point lo 4 1024 619+point lo 4 1024 620)/2)
    have hp : initialPayment 619 = (310959427640:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 619+point lo 4 1024 620)/2 = (158991379:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158991379:ℝ)/42188800) = (67942400:ℝ)/52988909 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_619
  · change initialPayment 620 ≤ initialValue ((point lo 4 1024 620+point lo 4 1024 621)/2)
    have hp : initialPayment 620 = (311607516667:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 620+point lo 4 1024 621)/2 = (159015517:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159015517:ℝ)/42188800) = (67942400:ℝ)/52964771 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_620
  · change initialPayment 621 ≤ initialValue ((point lo 4 1024 621+point lo 4 1024 622)/2)
    have hp : initialPayment 621 = (312256164800:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 621+point lo 4 1024 622)/2 = (31807931:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31807931:ℝ)/8437760) = (67942400:ℝ)/52940633 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_621
  · change initialPayment 622 ≤ initialValue ((point lo 4 1024 622+point lo 4 1024 623)/2)
    have hp : initialPayment 622 = (312905372566:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 622+point lo 4 1024 623)/2 = (159063793:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159063793:ℝ)/42188800) = (13588480:ℝ)/10583299 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_622
  · change initialPayment 623 ≤ initialValue ((point lo 4 1024 623+point lo 4 1024 624)/2)
    have hp : initialPayment 623 = (313555140491:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 623+point lo 4 1024 624)/2 = (159087931:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159087931:ℝ)/42188800) = (67942400:ℝ)/52892357 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_623
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_038
