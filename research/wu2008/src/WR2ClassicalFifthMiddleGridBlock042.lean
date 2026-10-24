import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints042
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_042 (j : Fin 16) : middlePayment (16*42+j.val) ≤
    middleValue ((point 4 cut 1024 (16*42+j.val)+point 4 cut 1024 (16*42+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 672 ≤ middleValue ((point 4 cut 1024 672+point 4 cut 1024 673)/2)
    have hp : middlePayment 672 = (652012412124:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 672+point 4 cut 1024 673)/2 = (16943577:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16943577:ℝ)/4218880) = (33971200:ℝ)/21272259 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16943577:ℝ)/4218880)-4 = (68057:ℝ)/4218880 by norm_num]
    exact paid_middle_672
  · change middlePayment 673 ≤ middleValue ((point 4 cut 1024 673+point 4 cut 1024 674)/2)
    have hp : middlePayment 673 = (652052319901:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 673+point 4 cut 1024 674)/2 = (84718391:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84718391:ℝ)/21094400) = (33971200:ℝ)/21271753 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84718391:ℝ)/21094400)-4 = (340791:ℝ)/21094400 by norm_num]
    exact paid_middle_673
  · change middlePayment 674 ≤ middleValue ((point 4 cut 1024 674+point 4 cut 1024 675)/2)
    have hp : middlePayment 674 = (652092229232:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 674+point 4 cut 1024 675)/2 = (84718897:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84718897:ℝ)/21094400) = (33971200:ℝ)/21271247 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84718897:ℝ)/21094400)-4 = (341297:ℝ)/21094400 by norm_num]
    exact paid_middle_674
  · change middlePayment 675 ≤ middleValue ((point 4 cut 1024 675+point 4 cut 1024 676)/2)
    have hp : middlePayment 675 = (652132140118:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 675+point 4 cut 1024 676)/2 = (84719403:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84719403:ℝ)/21094400) = (33971200:ℝ)/21270741 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84719403:ℝ)/21094400)-4 = (341803:ℝ)/21094400 by norm_num]
    exact paid_middle_675
  · change middlePayment 676 ≤ middleValue ((point 4 cut 1024 676+point 4 cut 1024 677)/2)
    have hp : middlePayment 676 = (652172052559:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 676+point 4 cut 1024 677)/2 = (84719909:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84719909:ℝ)/21094400) = (6794240:ℝ)/4254047 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84719909:ℝ)/21094400)-4 = (342309:ℝ)/21094400 by norm_num]
    exact paid_middle_676
  · change middlePayment 677 ≤ middleValue ((point 4 cut 1024 677+point 4 cut 1024 678)/2)
    have hp : middlePayment 677 = (652211966556:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 677+point 4 cut 1024 678)/2 = (16944083:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16944083:ℝ)/4218880) = (33971200:ℝ)/21269729 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16944083:ℝ)/4218880)-4 = (68563:ℝ)/4218880 by norm_num]
    exact paid_middle_677
  · change middlePayment 678 ≤ middleValue ((point 4 cut 1024 678+point 4 cut 1024 679)/2)
    have hp : middlePayment 678 = (652251882107:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 678+point 4 cut 1024 679)/2 = (84720921:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84720921:ℝ)/21094400) = (33971200:ℝ)/21269223 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84720921:ℝ)/21094400)-4 = (343321:ℝ)/21094400 by norm_num]
    exact paid_middle_678
  · change middlePayment 679 ≤ middleValue ((point 4 cut 1024 679+point 4 cut 1024 680)/2)
    have hp : middlePayment 679 = (652291799213:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 679+point 4 cut 1024 680)/2 = (84721427:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84721427:ℝ)/21094400) = (33971200:ℝ)/21268717 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84721427:ℝ)/21094400)-4 = (343827:ℝ)/21094400 by norm_num]
    exact paid_middle_679
  · change middlePayment 680 ≤ middleValue ((point 4 cut 1024 680+point 4 cut 1024 681)/2)
    have hp : middlePayment 680 = (652331717875:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 680+point 4 cut 1024 681)/2 = (84721933:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84721933:ℝ)/21094400) = (33971200:ℝ)/21268211 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84721933:ℝ)/21094400)-4 = (344333:ℝ)/21094400 by norm_num]
    exact paid_middle_680
  · change middlePayment 681 ≤ middleValue ((point 4 cut 1024 681+point 4 cut 1024 682)/2)
    have hp : middlePayment 681 = (652371638092:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 681+point 4 cut 1024 682)/2 = (84722439:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84722439:ℝ)/21094400) = (6794240:ℝ)/4253541 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84722439:ℝ)/21094400)-4 = (344839:ℝ)/21094400 by norm_num]
    exact paid_middle_681
  · change middlePayment 682 ≤ middleValue ((point 4 cut 1024 682+point 4 cut 1024 683)/2)
    have hp : middlePayment 682 = (652411559864:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 682+point 4 cut 1024 683)/2 = (16944589:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16944589:ℝ)/4218880) = (33971200:ℝ)/21267199 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16944589:ℝ)/4218880)-4 = (69069:ℝ)/4218880 by norm_num]
    exact paid_middle_682
  · change middlePayment 683 ≤ middleValue ((point 4 cut 1024 683+point 4 cut 1024 684)/2)
    have hp : middlePayment 683 = (652451483192:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 683+point 4 cut 1024 684)/2 = (84723451:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84723451:ℝ)/21094400) = (33971200:ℝ)/21266693 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84723451:ℝ)/21094400)-4 = (345851:ℝ)/21094400 by norm_num]
    exact paid_middle_683
  · change middlePayment 684 ≤ middleValue ((point 4 cut 1024 684+point 4 cut 1024 685)/2)
    have hp : middlePayment 684 = (652491408076:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 684+point 4 cut 1024 685)/2 = (84723957:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84723957:ℝ)/21094400) = (33971200:ℝ)/21266187 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84723957:ℝ)/21094400)-4 = (346357:ℝ)/21094400 by norm_num]
    exact paid_middle_684
  · change middlePayment 685 ≤ middleValue ((point 4 cut 1024 685+point 4 cut 1024 686)/2)
    have hp : middlePayment 685 = (652531334515:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 685+point 4 cut 1024 686)/2 = (84724463:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84724463:ℝ)/21094400) = (33971200:ℝ)/21265681 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84724463:ℝ)/21094400)-4 = (346863:ℝ)/21094400 by norm_num]
    exact paid_middle_685
  · change middlePayment 686 ≤ middleValue ((point 4 cut 1024 686+point 4 cut 1024 687)/2)
    have hp : middlePayment 686 = (652571262510:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 686+point 4 cut 1024 687)/2 = (84724969:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84724969:ℝ)/21094400) = (1024:ℝ)/641 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84724969:ℝ)/21094400)-4 = (347369:ℝ)/21094400 by norm_num]
    exact paid_middle_686
  · change middlePayment 687 ≤ middleValue ((point 4 cut 1024 687+point 4 cut 1024 688)/2)
    have hp : middlePayment 687 = (652611192061:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 687+point 4 cut 1024 688)/2 = (3389019:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3389019:ℝ)/843776) = (33971200:ℝ)/21264669 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3389019:ℝ)/843776)-4 = (13915:ℝ)/843776 by norm_num]
    exact paid_middle_687
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_042
