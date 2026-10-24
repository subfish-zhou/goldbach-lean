import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints039
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_039 (j : Fin 16) : middlePayment (16*39+j.val) ≤
    middleValue ((point 4 cut 1024 (16*39+j.val)+point 4 cut 1024 (16*39+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 624 ≤ middleValue ((point 4 cut 1024 624+point 4 cut 1024 625)/2)
    have hp : middlePayment 624 = (650098665746:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 624+point 4 cut 1024 625)/2 = (84693597:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84693597:ℝ)/21094400) = (33971200:ℝ)/21296547 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84693597:ℝ)/21094400)-4 = (315997:ℝ)/21094400 by norm_num]
    exact paid_middle_624
  · change middlePayment 625 ≤ middleValue ((point 4 cut 1024 625+point 4 cut 1024 626)/2)
    have hp : middlePayment 625 = (650138498985:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 625+point 4 cut 1024 626)/2 = (84694103:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84694103:ℝ)/21094400) = (33971200:ℝ)/21296041 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84694103:ℝ)/21094400)-4 = (316503:ℝ)/21094400 by norm_num]
    exact paid_middle_625
  · change middlePayment 626 ≤ middleValue ((point 4 cut 1024 626+point 4 cut 1024 627)/2)
    have hp : middlePayment 626 = (650178333775:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 626+point 4 cut 1024 627)/2 = (84694609:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84694609:ℝ)/21094400) = (6794240:ℝ)/4259107 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84694609:ℝ)/21094400)-4 = (317009:ℝ)/21094400 by norm_num]
    exact paid_middle_626
  · change middlePayment 627 ≤ middleValue ((point 4 cut 1024 627+point 4 cut 1024 628)/2)
    have hp : middlePayment 627 = (650218170116:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 627+point 4 cut 1024 628)/2 = (16939023:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16939023:ℝ)/4218880) = (33971200:ℝ)/21295029 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16939023:ℝ)/4218880)-4 = (63503:ℝ)/4218880 by norm_num]
    exact paid_middle_627
  · change middlePayment 628 ≤ middleValue ((point 4 cut 1024 628+point 4 cut 1024 629)/2)
    have hp : middlePayment 628 = (650258008008:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 628+point 4 cut 1024 629)/2 = (84695621:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84695621:ℝ)/21094400) = (33971200:ℝ)/21294523 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84695621:ℝ)/21094400)-4 = (318021:ℝ)/21094400 by norm_num]
    exact paid_middle_628
  · change middlePayment 629 ≤ middleValue ((point 4 cut 1024 629+point 4 cut 1024 630)/2)
    have hp : middlePayment 629 = (650297847452:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 629+point 4 cut 1024 630)/2 = (84696127:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84696127:ℝ)/21094400) = (33971200:ℝ)/21294017 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84696127:ℝ)/21094400)-4 = (318527:ℝ)/21094400 by norm_num]
    exact paid_middle_629
  · change middlePayment 630 ≤ middleValue ((point 4 cut 1024 630+point 4 cut 1024 631)/2)
    have hp : middlePayment 630 = (650337688447:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 630+point 4 cut 1024 631)/2 = (84696633:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84696633:ℝ)/21094400) = (33971200:ℝ)/21293511 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84696633:ℝ)/21094400)-4 = (319033:ℝ)/21094400 by norm_num]
    exact paid_middle_630
  · change middlePayment 631 ≤ middleValue ((point 4 cut 1024 631+point 4 cut 1024 632)/2)
    have hp : middlePayment 631 = (650377530993:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 631+point 4 cut 1024 632)/2 = (84697139:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84697139:ℝ)/21094400) = (6794240:ℝ)/4258601 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84697139:ℝ)/21094400)-4 = (319539:ℝ)/21094400 by norm_num]
    exact paid_middle_631
  · change middlePayment 632 ≤ middleValue ((point 4 cut 1024 632+point 4 cut 1024 633)/2)
    have hp : middlePayment 632 = (650417375091:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 632+point 4 cut 1024 633)/2 = (16939529:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16939529:ℝ)/4218880) = (33971200:ℝ)/21292499 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16939529:ℝ)/4218880)-4 = (64009:ℝ)/4218880 by norm_num]
    exact paid_middle_632
  · change middlePayment 633 ≤ middleValue ((point 4 cut 1024 633+point 4 cut 1024 634)/2)
    have hp : middlePayment 633 = (650457220740:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 633+point 4 cut 1024 634)/2 = (84698151:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84698151:ℝ)/21094400) = (33971200:ℝ)/21291993 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84698151:ℝ)/21094400)-4 = (320551:ℝ)/21094400 by norm_num]
    exact paid_middle_633
  · change middlePayment 634 ≤ middleValue ((point 4 cut 1024 634+point 4 cut 1024 635)/2)
    have hp : middlePayment 634 = (650497067941:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 634+point 4 cut 1024 635)/2 = (84698657:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84698657:ℝ)/21094400) = (33971200:ℝ)/21291487 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84698657:ℝ)/21094400)-4 = (321057:ℝ)/21094400 by norm_num]
    exact paid_middle_634
  · change middlePayment 635 ≤ middleValue ((point 4 cut 1024 635+point 4 cut 1024 636)/2)
    have hp : middlePayment 635 = (650536916694:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 635+point 4 cut 1024 636)/2 = (84699163:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84699163:ℝ)/21094400) = (33971200:ℝ)/21290981 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84699163:ℝ)/21094400)-4 = (321563:ℝ)/21094400 by norm_num]
    exact paid_middle_635
  · change middlePayment 636 ≤ middleValue ((point 4 cut 1024 636+point 4 cut 1024 637)/2)
    have hp : middlePayment 636 = (650576766998:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 636+point 4 cut 1024 637)/2 = (84699669:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84699669:ℝ)/21094400) = (1358848:ℝ)/851619 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84699669:ℝ)/21094400)-4 = (322069:ℝ)/21094400 by norm_num]
    exact paid_middle_636
  · change middlePayment 637 ≤ middleValue ((point 4 cut 1024 637+point 4 cut 1024 638)/2)
    have hp : middlePayment 637 = (650616618855:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 637+point 4 cut 1024 638)/2 = (3388007:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3388007:ℝ)/843776) = (33971200:ℝ)/21289969 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3388007:ℝ)/843776)-4 = (12903:ℝ)/843776 by norm_num]
    exact paid_middle_637
  · change middlePayment 638 ≤ middleValue ((point 4 cut 1024 638+point 4 cut 1024 639)/2)
    have hp : middlePayment 638 = (650656472263:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 638+point 4 cut 1024 639)/2 = (84700681:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84700681:ℝ)/21094400) = (33971200:ℝ)/21289463 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84700681:ℝ)/21094400)-4 = (323081:ℝ)/21094400 by norm_num]
    exact paid_middle_638
  · change middlePayment 639 ≤ middleValue ((point 4 cut 1024 639+point 4 cut 1024 640)/2)
    have hp : middlePayment 639 = (650696327224:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 639+point 4 cut 1024 640)/2 = (84701187:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84701187:ℝ)/21094400) = (33971200:ℝ)/21288957 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84701187:ℝ)/21094400)-4 = (323587:ℝ)/21094400 by norm_num]
    exact paid_middle_639
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_039
