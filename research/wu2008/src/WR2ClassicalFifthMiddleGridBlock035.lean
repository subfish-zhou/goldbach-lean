import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints035
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_035 (j : Fin 16) : middlePayment (16*35+j.val) ≤
    middleValue ((point 4 cut 1024 (16*35+j.val)+point 4 cut 1024 (16*35+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 560 ≤ middleValue ((point 4 cut 1024 560+point 4 cut 1024 561)/2)
    have hp : middlePayment 560 = (647552560972:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 560+point 4 cut 1024 561)/2 = (84661213:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84661213:ℝ)/21094400) = (33971200:ℝ)/21328931 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84661213:ℝ)/21094400)-4 = (283613:ℝ)/21094400 by norm_num]
    exact paid_middle_560
  · change middlePayment 561 ≤ middleValue ((point 4 cut 1024 561+point 4 cut 1024 562)/2)
    have hp : middlePayment 561 = (647592295109:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 561+point 4 cut 1024 562)/2 = (84661719:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84661719:ℝ)/21094400) = (1358848:ℝ)/853137 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84661719:ℝ)/21094400)-4 = (284119:ℝ)/21094400 by norm_num]
    exact paid_middle_561
  · change middlePayment 562 ≤ middleValue ((point 4 cut 1024 562+point 4 cut 1024 563)/2)
    have hp : middlePayment 562 = (647632030792:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 562+point 4 cut 1024 563)/2 = (3386489:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3386489:ℝ)/843776) = (33971200:ℝ)/21327919 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3386489:ℝ)/843776)-4 = (11385:ℝ)/843776 by norm_num]
    exact paid_middle_562
  · change middlePayment 563 ≤ middleValue ((point 4 cut 1024 563+point 4 cut 1024 564)/2)
    have hp : middlePayment 563 = (647671768021:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 563+point 4 cut 1024 564)/2 = (84662731:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84662731:ℝ)/21094400) = (33971200:ℝ)/21327413 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84662731:ℝ)/21094400)-4 = (285131:ℝ)/21094400 by norm_num]
    exact paid_middle_563
  · change middlePayment 564 ≤ middleValue ((point 4 cut 1024 564+point 4 cut 1024 565)/2)
    have hp : middlePayment 564 = (647711506797:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 564+point 4 cut 1024 565)/2 = (84663237:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84663237:ℝ)/21094400) = (33971200:ℝ)/21326907 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84663237:ℝ)/21094400)-4 = (285637:ℝ)/21094400 by norm_num]
    exact paid_middle_564
  · change middlePayment 565 ≤ middleValue ((point 4 cut 1024 565+point 4 cut 1024 566)/2)
    have hp : middlePayment 565 = (647751247118:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 565+point 4 cut 1024 566)/2 = (84663743:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84663743:ℝ)/21094400) = (33971200:ℝ)/21326401 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84663743:ℝ)/21094400)-4 = (286143:ℝ)/21094400 by norm_num]
    exact paid_middle_565
  · change middlePayment 566 ≤ middleValue ((point 4 cut 1024 566+point 4 cut 1024 567)/2)
    have hp : middlePayment 566 = (647790988986:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 566+point 4 cut 1024 567)/2 = (821983:ℝ)/204800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((821983:ℝ)/204800) = (6794240:ℝ)/4265179 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((821983:ℝ)/204800)-4 = (2783:ℝ)/204800 by norm_num]
    exact paid_middle_566
  · change middlePayment 567 ≤ middleValue ((point 4 cut 1024 567+point 4 cut 1024 568)/2)
    have hp : middlePayment 567 = (647830732401:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 567+point 4 cut 1024 568)/2 = (16932951:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16932951:ℝ)/4218880) = (33971200:ℝ)/21325389 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16932951:ℝ)/4218880)-4 = (57431:ℝ)/4218880 by norm_num]
    exact paid_middle_567
  · change middlePayment 568 ≤ middleValue ((point 4 cut 1024 568+point 4 cut 1024 569)/2)
    have hp : middlePayment 568 = (647870477361:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 568+point 4 cut 1024 569)/2 = (84665261:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84665261:ℝ)/21094400) = (33971200:ℝ)/21324883 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84665261:ℝ)/21094400)-4 = (287661:ℝ)/21094400 by norm_num]
    exact paid_middle_568
  · change middlePayment 569 ≤ middleValue ((point 4 cut 1024 569+point 4 cut 1024 570)/2)
    have hp : middlePayment 569 = (647910223869:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 569+point 4 cut 1024 570)/2 = (84665767:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84665767:ℝ)/21094400) = (33971200:ℝ)/21324377 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84665767:ℝ)/21094400)-4 = (288167:ℝ)/21094400 by norm_num]
    exact paid_middle_569
  · change middlePayment 570 ≤ middleValue ((point 4 cut 1024 570+point 4 cut 1024 571)/2)
    have hp : middlePayment 570 = (647949971923:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 570+point 4 cut 1024 571)/2 = (84666273:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84666273:ℝ)/21094400) = (33971200:ℝ)/21323871 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84666273:ℝ)/21094400)-4 = (288673:ℝ)/21094400 by norm_num]
    exact paid_middle_570
  · change middlePayment 571 ≤ middleValue ((point 4 cut 1024 571+point 4 cut 1024 572)/2)
    have hp : middlePayment 571 = (647989721523:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 571+point 4 cut 1024 572)/2 = (84666779:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84666779:ℝ)/21094400) = (6794240:ℝ)/4264673 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84666779:ℝ)/21094400)-4 = (289179:ℝ)/21094400 by norm_num]
    exact paid_middle_571
  · change middlePayment 572 ≤ middleValue ((point 4 cut 1024 572+point 4 cut 1024 573)/2)
    have hp : middlePayment 572 = (648029472671:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 572+point 4 cut 1024 573)/2 = (16933457:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16933457:ℝ)/4218880) = (33971200:ℝ)/21322859 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16933457:ℝ)/4218880)-4 = (57937:ℝ)/4218880 by norm_num]
    exact paid_middle_572
  · change middlePayment 573 ≤ middleValue ((point 4 cut 1024 573+point 4 cut 1024 574)/2)
    have hp : middlePayment 573 = (648069225365:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 573+point 4 cut 1024 574)/2 = (84667791:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84667791:ℝ)/21094400) = (33971200:ℝ)/21322353 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84667791:ℝ)/21094400)-4 = (290191:ℝ)/21094400 by norm_num]
    exact paid_middle_573
  · change middlePayment 574 ≤ middleValue ((point 4 cut 1024 574+point 4 cut 1024 575)/2)
    have hp : middlePayment 574 = (648108979606:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 574+point 4 cut 1024 575)/2 = (84668297:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84668297:ℝ)/21094400) = (33971200:ℝ)/21321847 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84668297:ℝ)/21094400)-4 = (290697:ℝ)/21094400 by norm_num]
    exact paid_middle_574
  · change middlePayment 575 ≤ middleValue ((point 4 cut 1024 575+point 4 cut 1024 576)/2)
    have hp : middlePayment 575 = (648148735394:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 575+point 4 cut 1024 576)/2 = (84668803:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84668803:ℝ)/21094400) = (33971200:ℝ)/21321341 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84668803:ℝ)/21094400)-4 = (291203:ℝ)/21094400 by norm_num]
    exact paid_middle_575
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_035
