import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints039
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_039 (j : Fin 16) : initialPayment (16*39+j.val) ≤
    initialValue ((point lo 4 1024 (16*39+j.val)+point lo 4 1024 (16*39+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 624 ≤ initialValue ((point lo 4 1024 624+point lo 4 1024 625)/2)
    have hp : initialPayment 624 = (314205469107:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 624+point lo 4 1024 625)/2 = (159112069:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159112069:ℝ)/42188800) = (67942400:ℝ)/52868219 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_624
  · change initialPayment 625 ≤ initialValue ((point lo 4 1024 625+point lo 4 1024 626)/2)
    have hp : initialPayment 625 = (314856358941:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 625+point lo 4 1024 626)/2 = (159136207:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159136207:ℝ)/42188800) = (67942400:ℝ)/52844081 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_625
  · change initialPayment 626 ≤ initialValue ((point lo 4 1024 626+point lo 4 1024 627)/2)
    have hp : initialPayment 626 = (315507810525:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 626+point lo 4 1024 627)/2 = (31832069:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31832069:ℝ)/8437760) = (67942400:ℝ)/52819943 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_626
  · change initialPayment 627 ≤ initialValue ((point lo 4 1024 627+point lo 4 1024 628)/2)
    have hp : initialPayment 627 = (316159824390:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 627+point lo 4 1024 628)/2 = (159184483:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159184483:ℝ)/42188800) = (13588480:ℝ)/10559161 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_627
  · change initialPayment 628 ≤ initialValue ((point lo 4 1024 628+point lo 4 1024 629)/2)
    have hp : initialPayment 628 = (316812401068:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 628+point lo 4 1024 629)/2 = (159208621:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159208621:ℝ)/42188800) = (67942400:ℝ)/52771667 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_628
  · change initialPayment 629 ≤ initialValue ((point lo 4 1024 629+point lo 4 1024 630)/2)
    have hp : initialPayment 629 = (317465541091:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 629+point lo 4 1024 630)/2 = (159232759:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159232759:ℝ)/42188800) = (67942400:ℝ)/52747529 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_629
  · change initialPayment 630 ≤ initialValue ((point lo 4 1024 630+point lo 4 1024 631)/2)
    have hp : initialPayment 630 = (318119244994:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 630+point lo 4 1024 631)/2 = (159256897:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159256897:ℝ)/42188800) = (67942400:ℝ)/52723391 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_630
  · change initialPayment 631 ≤ initialValue ((point lo 4 1024 631+point lo 4 1024 632)/2)
    have hp : initialPayment 631 = (318773513310:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 631+point lo 4 1024 632)/2 = (31856207:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31856207:ℝ)/8437760) = (67942400:ℝ)/52699253 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_631
  · change initialPayment 632 ≤ initialValue ((point lo 4 1024 632+point lo 4 1024 633)/2)
    have hp : initialPayment 632 = (319428346575:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 632+point lo 4 1024 633)/2 = (159305173:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159305173:ℝ)/42188800) = (13588480:ℝ)/10535023 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_632
  · change initialPayment 633 ≤ initialValue ((point lo 4 1024 633+point lo 4 1024 634)/2)
    have hp : initialPayment 633 = (320083745326:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 633+point lo 4 1024 634)/2 = (159329311:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159329311:ℝ)/42188800) = (67942400:ℝ)/52650977 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_633
  · change initialPayment 634 ≤ initialValue ((point lo 4 1024 634+point lo 4 1024 635)/2)
    have hp : initialPayment 634 = (320739710098:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 634+point lo 4 1024 635)/2 = (159353449:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159353449:ℝ)/42188800) = (67942400:ℝ)/52626839 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_634
  · change initialPayment 635 ≤ initialValue ((point lo 4 1024 635+point lo 4 1024 636)/2)
    have hp : initialPayment 635 = (321396241430:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 635+point lo 4 1024 636)/2 = (159377587:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159377587:ℝ)/42188800) = (67942400:ℝ)/52602701 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_635
  · change initialPayment 636 ≤ initialValue ((point lo 4 1024 636+point lo 4 1024 637)/2)
    have hp : initialPayment 636 = (322053339860:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 636+point lo 4 1024 637)/2 = (6376069:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6376069:ℝ)/1687552) = (67942400:ℝ)/52578563 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_636
  · change initialPayment 637 ≤ initialValue ((point lo 4 1024 637+point lo 4 1024 638)/2)
    have hp : initialPayment 637 = (322711005927:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 637+point lo 4 1024 638)/2 = (159425863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159425863:ℝ)/42188800) = (2717696:ℝ)/2102177 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_637
  · change initialPayment 638 ≤ initialValue ((point lo 4 1024 638+point lo 4 1024 639)/2)
    have hp : initialPayment 638 = (323369240172:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 638+point lo 4 1024 639)/2 = (159450001:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159450001:ℝ)/42188800) = (67942400:ℝ)/52530287 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_638
  · change initialPayment 639 ≤ initialValue ((point lo 4 1024 639+point lo 4 1024 640)/2)
    have hp : initialPayment 639 = (324028043135:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 639+point lo 4 1024 640)/2 = (159474139:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159474139:ℝ)/42188800) = (67942400:ℝ)/52506149 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_639
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_039
