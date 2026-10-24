import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints036
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_036 (j : Fin 16) : initialPayment (16*36+j.val) ≤
    initialValue ((point lo 4 1024 (16*36+j.val)+point lo 4 1024 (16*36+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 576 ≤ initialValue ((point lo 4 1024 576+point lo 4 1024 577)/2)
    have hp : initialPayment 576 = (283613158425:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 576+point lo 4 1024 577)/2 = (31590689:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31590689:ℝ)/8437760) = (67942400:ℝ)/54026843 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_576
  · change initialPayment 577 ≤ initialValue ((point lo 4 1024 577+point lo 4 1024 578)/2)
    have hp : initialPayment 577 = (284237693691:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 577+point lo 4 1024 578)/2 = (157977583:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157977583:ℝ)/42188800) = (13588480:ℝ)/10800541 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_577
  · change initialPayment 578 ≤ initialValue ((point lo 4 1024 578+point lo 4 1024 579)/2)
    have hp : initialPayment 578 = (284862766120:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 578+point lo 4 1024 579)/2 = (158001721:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158001721:ℝ)/42188800) = (67942400:ℝ)/53978567 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_578
  · change initialPayment 579 ≤ initialValue ((point lo 4 1024 579+point lo 4 1024 580)/2)
    have hp : initialPayment 579 = (285488376207:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 579+point lo 4 1024 580)/2 = (158025859:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158025859:ℝ)/42188800) = (67942400:ℝ)/53954429 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_579
  · change initialPayment 580 ≤ initialValue ((point lo 4 1024 580+point lo 4 1024 581)/2)
    have hp : initialPayment 580 = (286114524448:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 580+point lo 4 1024 581)/2 = (158049997:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158049997:ℝ)/42188800) = (67942400:ℝ)/53930291 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_580
  · change initialPayment 581 ≤ initialValue ((point lo 4 1024 581+point lo 4 1024 582)/2)
    have hp : initialPayment 581 = (286741211338:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 581+point lo 4 1024 582)/2 = (31614827:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31614827:ℝ)/8437760) = (67942400:ℝ)/53906153 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_581
  · change initialPayment 582 ≤ initialValue ((point lo 4 1024 582+point lo 4 1024 583)/2)
    have hp : initialPayment 582 = (287368437374:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 582+point lo 4 1024 583)/2 = (158098273:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158098273:ℝ)/42188800) = (13588480:ℝ)/10776403 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_582
  · change initialPayment 583 ≤ initialValue ((point lo 4 1024 583+point lo 4 1024 584)/2)
    have hp : initialPayment 583 = (287996203053:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 583+point lo 4 1024 584)/2 = (158122411:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158122411:ℝ)/42188800) = (67942400:ℝ)/53857877 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_583
  · change initialPayment 584 ≤ initialValue ((point lo 4 1024 584+point lo 4 1024 585)/2)
    have hp : initialPayment 584 = (288624508874:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 584+point lo 4 1024 585)/2 = (158146549:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158146549:ℝ)/42188800) = (67942400:ℝ)/53833739 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_584
  · change initialPayment 585 ≤ initialValue ((point lo 4 1024 585+point lo 4 1024 586)/2)
    have hp : initialPayment 585 = (289253355335:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 585+point lo 4 1024 586)/2 = (158170687:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158170687:ℝ)/42188800) = (67942400:ℝ)/53809601 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_585
  · change initialPayment 586 ≤ initialValue ((point lo 4 1024 586+point lo 4 1024 587)/2)
    have hp : initialPayment 586 = (289882742936:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 586+point lo 4 1024 587)/2 = (6327793:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6327793:ℝ)/1687552) = (67942400:ℝ)/53785463 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_586
  · change initialPayment 587 ≤ initialValue ((point lo 4 1024 587+point lo 4 1024 588)/2)
    have hp : initialPayment 587 = (290512672177:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 587+point lo 4 1024 588)/2 = (158218963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158218963:ℝ)/42188800) = (2717696:ℝ)/2150453 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_587
  · change initialPayment 588 ≤ initialValue ((point lo 4 1024 588+point lo 4 1024 589)/2)
    have hp : initialPayment 588 = (291143143560:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 588+point lo 4 1024 589)/2 = (158243101:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158243101:ℝ)/42188800) = (67942400:ℝ)/53737187 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_588
  · change initialPayment 589 ≤ initialValue ((point lo 4 1024 589+point lo 4 1024 590)/2)
    have hp : initialPayment 589 = (291774157586:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 589+point lo 4 1024 590)/2 = (158267239:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158267239:ℝ)/42188800) = (67942400:ℝ)/53713049 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_589
  · change initialPayment 590 ≤ initialValue ((point lo 4 1024 590+point lo 4 1024 591)/2)
    have hp : initialPayment 590 = (292405714758:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 590+point lo 4 1024 591)/2 = (158291377:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((158291377:ℝ)/42188800) = (67942400:ℝ)/53688911 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_590
  · change initialPayment 591 ≤ initialValue ((point lo 4 1024 591+point lo 4 1024 592)/2)
    have hp : initialPayment 591 = (293037815578:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 591+point lo 4 1024 592)/2 = (31663103:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31663103:ℝ)/8437760) = (67942400:ℝ)/53664773 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_591
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_036
