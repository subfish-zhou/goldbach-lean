import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints041
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_041 (j : Fin 16) : middlePayment (16*41+j.val) ≤
    middleValue ((point 4 cut 1024 (16*41+j.val)+point 4 cut 1024 (16*41+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 656 ≤ middleValue ((point 4 cut 1024 656+point 4 cut 1024 657)/2)
    have hp : middlePayment 656 = (651374099088:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 656+point 4 cut 1024 657)/2 = (84709789:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84709789:ℝ)/21094400) = (6794240:ℝ)/4256071 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84709789:ℝ)/21094400)-4 = (332189:ℝ)/21094400 by norm_num]
    exact paid_middle_656
  · change middlePayment 657 ≤ middleValue ((point 4 cut 1024 657+point 4 cut 1024 658)/2)
    have hp : middlePayment 657 = (651413981999:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 657+point 4 cut 1024 658)/2 = (16942059:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16942059:ℝ)/4218880) = (33971200:ℝ)/21279849 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16942059:ℝ)/4218880)-4 = (66539:ℝ)/4218880 by norm_num]
    exact paid_middle_657
  · change middlePayment 658 ≤ middleValue ((point 4 cut 1024 658+point 4 cut 1024 659)/2)
    have hp : middlePayment 658 = (651453866463:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 658+point 4 cut 1024 659)/2 = (84710801:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84710801:ℝ)/21094400) = (33971200:ℝ)/21279343 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84710801:ℝ)/21094400)-4 = (333201:ℝ)/21094400 by norm_num]
    exact paid_middle_658
  · change middlePayment 659 ≤ middleValue ((point 4 cut 1024 659+point 4 cut 1024 660)/2)
    have hp : middlePayment 659 = (651493752480:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 659+point 4 cut 1024 660)/2 = (84711307:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84711307:ℝ)/21094400) = (33971200:ℝ)/21278837 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84711307:ℝ)/21094400)-4 = (333707:ℝ)/21094400 by norm_num]
    exact paid_middle_659
  · change middlePayment 660 ≤ middleValue ((point 4 cut 1024 660+point 4 cut 1024 661)/2)
    have hp : middlePayment 660 = (651533640052:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 660+point 4 cut 1024 661)/2 = (84711813:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84711813:ℝ)/21094400) = (33971200:ℝ)/21278331 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84711813:ℝ)/21094400)-4 = (334213:ℝ)/21094400 by norm_num]
    exact paid_middle_660
  · change middlePayment 661 ≤ middleValue ((point 4 cut 1024 661+point 4 cut 1024 662)/2)
    have hp : middlePayment 661 = (651573529177:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 661+point 4 cut 1024 662)/2 = (84712319:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84712319:ℝ)/21094400) = (1358848:ℝ)/851113 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84712319:ℝ)/21094400)-4 = (334719:ℝ)/21094400 by norm_num]
    exact paid_middle_661
  · change middlePayment 662 ≤ middleValue ((point 4 cut 1024 662+point 4 cut 1024 663)/2)
    have hp : middlePayment 662 = (651613419856:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 662+point 4 cut 1024 663)/2 = (3388513:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3388513:ℝ)/843776) = (33971200:ℝ)/21277319 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3388513:ℝ)/843776)-4 = (13409:ℝ)/843776 by norm_num]
    exact paid_middle_662
  · change middlePayment 663 ≤ middleValue ((point 4 cut 1024 663+point 4 cut 1024 664)/2)
    have hp : middlePayment 663 = (651653312089:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 663+point 4 cut 1024 664)/2 = (84713331:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84713331:ℝ)/21094400) = (33971200:ℝ)/21276813 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84713331:ℝ)/21094400)-4 = (335731:ℝ)/21094400 by norm_num]
    exact paid_middle_663
  · change middlePayment 664 ≤ middleValue ((point 4 cut 1024 664+point 4 cut 1024 665)/2)
    have hp : middlePayment 664 = (651693205876:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 664+point 4 cut 1024 665)/2 = (84713837:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84713837:ℝ)/21094400) = (33971200:ℝ)/21276307 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84713837:ℝ)/21094400)-4 = (336237:ℝ)/21094400 by norm_num]
    exact paid_middle_664
  · change middlePayment 665 ≤ middleValue ((point 4 cut 1024 665+point 4 cut 1024 666)/2)
    have hp : middlePayment 665 = (651733101217:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 665+point 4 cut 1024 666)/2 = (84714343:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84714343:ℝ)/21094400) = (33971200:ℝ)/21275801 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84714343:ℝ)/21094400)-4 = (336743:ℝ)/21094400 by norm_num]
    exact paid_middle_665
  · change middlePayment 666 ≤ middleValue ((point 4 cut 1024 666+point 4 cut 1024 667)/2)
    have hp : middlePayment 666 = (651772998112:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 666+point 4 cut 1024 667)/2 = (84714849:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84714849:ℝ)/21094400) = (6794240:ℝ)/4255059 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84714849:ℝ)/21094400)-4 = (337249:ℝ)/21094400 by norm_num]
    exact paid_middle_666
  · change middlePayment 667 ≤ middleValue ((point 4 cut 1024 667+point 4 cut 1024 668)/2)
    have hp : middlePayment 667 = (651812896561:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 667+point 4 cut 1024 668)/2 = (16943071:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16943071:ℝ)/4218880) = (33971200:ℝ)/21274789 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16943071:ℝ)/4218880)-4 = (67551:ℝ)/4218880 by norm_num]
    exact paid_middle_667
  · change middlePayment 668 ≤ middleValue ((point 4 cut 1024 668+point 4 cut 1024 669)/2)
    have hp : middlePayment 668 = (651852796565:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 668+point 4 cut 1024 669)/2 = (84715861:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84715861:ℝ)/21094400) = (33971200:ℝ)/21274283 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84715861:ℝ)/21094400)-4 = (338261:ℝ)/21094400 by norm_num]
    exact paid_middle_668
  · change middlePayment 669 ≤ middleValue ((point 4 cut 1024 669+point 4 cut 1024 670)/2)
    have hp : middlePayment 669 = (651892698123:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 669+point 4 cut 1024 670)/2 = (822489:ℝ)/204800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((822489:ℝ)/204800) = (33971200:ℝ)/21273777 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((822489:ℝ)/204800)-4 = (3289:ℝ)/204800 by norm_num]
    exact paid_middle_669
  · change middlePayment 670 ≤ middleValue ((point 4 cut 1024 670+point 4 cut 1024 671)/2)
    have hp : middlePayment 670 = (651932601236:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 670+point 4 cut 1024 671)/2 = (84716873:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84716873:ℝ)/21094400) = (33971200:ℝ)/21273271 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84716873:ℝ)/21094400)-4 = (339273:ℝ)/21094400 by norm_num]
    exact paid_middle_670
  · change middlePayment 671 ≤ middleValue ((point 4 cut 1024 671+point 4 cut 1024 672)/2)
    have hp : middlePayment 671 = (651972505903:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 671+point 4 cut 1024 672)/2 = (84717379:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84717379:ℝ)/21094400) = (6794240:ℝ)/4254553 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84717379:ℝ)/21094400)-4 = (339779:ℝ)/21094400 by norm_num]
    exact paid_middle_671
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_041
