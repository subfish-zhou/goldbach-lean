import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints000
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_000 (j : Fin 16) : middlePayment (16*0+j.val) ≤
    middleValue ((point 4 cut 1024 (16*0+j.val)+point 4 cut 1024 (16*0+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 0 ≤ middleValue ((point 4 cut 1024 0+point 4 cut 1024 1)/2)
    have hp : middlePayment 0 = (625542012923:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 0+point 4 cut 1024 1)/2 = (84377853:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84377853:ℝ)/21094400) = (33971200:ℝ)/21612291 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84377853:ℝ)/21094400)-4 = (253:ℝ)/21094400 by norm_num]
    exact paid_middle_0
  · change middlePayment 1 ≤ middleValue ((point 4 cut 1024 1+point 4 cut 1024 2)/2)
    have hp : middlePayment 1 = (625580893414:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 1+point 4 cut 1024 2)/2 = (84378359:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84378359:ℝ)/21094400) = (6794240:ℝ)/4322357 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84378359:ℝ)/21094400)-4 = (759:ℝ)/21094400 by norm_num]
    exact paid_middle_1
  · change middlePayment 2 ≤ middleValue ((point 4 cut 1024 2+point 4 cut 1024 3)/2)
    have hp : middlePayment 2 = (625619775408:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 2+point 4 cut 1024 3)/2 = (16875773:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16875773:ℝ)/4218880) = (33971200:ℝ)/21611279 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16875773:ℝ)/4218880)-4 = (253:ℝ)/4218880 by norm_num]
    exact paid_middle_2
  · change middlePayment 3 ≤ middleValue ((point 4 cut 1024 3+point 4 cut 1024 4)/2)
    have hp : middlePayment 3 = (625658658905:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 3+point 4 cut 1024 4)/2 = (84379371:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84379371:ℝ)/21094400) = (33971200:ℝ)/21610773 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84379371:ℝ)/21094400)-4 = (1771:ℝ)/21094400 by norm_num]
    exact paid_middle_3
  · change middlePayment 4 ≤ middleValue ((point 4 cut 1024 4+point 4 cut 1024 5)/2)
    have hp : middlePayment 4 = (625697543905:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 4+point 4 cut 1024 5)/2 = (84379877:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84379877:ℝ)/21094400) = (33971200:ℝ)/21610267 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84379877:ℝ)/21094400)-4 = (2277:ℝ)/21094400 by norm_num]
    exact paid_middle_4
  · change middlePayment 5 ≤ middleValue ((point 4 cut 1024 5+point 4 cut 1024 6)/2)
    have hp : middlePayment 5 = (625736430408:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 5+point 4 cut 1024 6)/2 = (84380383:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84380383:ℝ)/21094400) = (33971200:ℝ)/21609761 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84380383:ℝ)/21094400)-4 = (2783:ℝ)/21094400 by norm_num]
    exact paid_middle_5
  · change middlePayment 6 ≤ middleValue ((point 4 cut 1024 6+point 4 cut 1024 7)/2)
    have hp : middlePayment 6 = (625775318415:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 6+point 4 cut 1024 7)/2 = (84380889:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84380889:ℝ)/21094400) = (6794240:ℝ)/4321851 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84380889:ℝ)/21094400)-4 = (3289:ℝ)/21094400 by norm_num]
    exact paid_middle_6
  · change middlePayment 7 ≤ middleValue ((point 4 cut 1024 7+point 4 cut 1024 8)/2)
    have hp : middlePayment 7 = (625814207926:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 7+point 4 cut 1024 8)/2 = (16876279:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16876279:ℝ)/4218880) = (33971200:ℝ)/21608749 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16876279:ℝ)/4218880)-4 = (759:ℝ)/4218880 by norm_num]
    exact paid_middle_7
  · change middlePayment 8 ≤ middleValue ((point 4 cut 1024 8+point 4 cut 1024 9)/2)
    have hp : middlePayment 8 = (625853098940:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 8+point 4 cut 1024 9)/2 = (84381901:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84381901:ℝ)/21094400) = (33971200:ℝ)/21608243 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84381901:ℝ)/21094400)-4 = (4301:ℝ)/21094400 by norm_num]
    exact paid_middle_8
  · change middlePayment 9 ≤ middleValue ((point 4 cut 1024 9+point 4 cut 1024 10)/2)
    have hp : middlePayment 9 = (625891991457:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 9+point 4 cut 1024 10)/2 = (84382407:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84382407:ℝ)/21094400) = (33971200:ℝ)/21607737 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84382407:ℝ)/21094400)-4 = (4807:ℝ)/21094400 by norm_num]
    exact paid_middle_9
  · change middlePayment 10 ≤ middleValue ((point 4 cut 1024 10+point 4 cut 1024 11)/2)
    have hp : middlePayment 10 = (625930885479:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 10+point 4 cut 1024 11)/2 = (84382913:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84382913:ℝ)/21094400) = (33971200:ℝ)/21607231 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84382913:ℝ)/21094400)-4 = (5313:ℝ)/21094400 by norm_num]
    exact paid_middle_10
  · change middlePayment 11 ≤ middleValue ((point 4 cut 1024 11+point 4 cut 1024 12)/2)
    have hp : middlePayment 11 = (625969781004:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 11+point 4 cut 1024 12)/2 = (84383419:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84383419:ℝ)/21094400) = (1358848:ℝ)/864269 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84383419:ℝ)/21094400)-4 = (5819:ℝ)/21094400 by norm_num]
    exact paid_middle_11
  · change middlePayment 12 ≤ middleValue ((point 4 cut 1024 12+point 4 cut 1024 13)/2)
    have hp : middlePayment 12 = (626008678033:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 12+point 4 cut 1024 13)/2 = (3375357:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3375357:ℝ)/843776) = (33971200:ℝ)/21606219 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3375357:ℝ)/843776)-4 = (253:ℝ)/843776 by norm_num]
    exact paid_middle_12
  · change middlePayment 13 ≤ middleValue ((point 4 cut 1024 13+point 4 cut 1024 14)/2)
    have hp : middlePayment 13 = (626047576566:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 13+point 4 cut 1024 14)/2 = (84384431:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84384431:ℝ)/21094400) = (33971200:ℝ)/21605713 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84384431:ℝ)/21094400)-4 = (6831:ℝ)/21094400 by norm_num]
    exact paid_middle_13
  · change middlePayment 14 ≤ middleValue ((point 4 cut 1024 14+point 4 cut 1024 15)/2)
    have hp : middlePayment 14 = (626086476603:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 14+point 4 cut 1024 15)/2 = (84384937:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84384937:ℝ)/21094400) = (33971200:ℝ)/21605207 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84384937:ℝ)/21094400)-4 = (7337:ℝ)/21094400 by norm_num]
    exact paid_middle_14
  · change middlePayment 15 ≤ middleValue ((point 4 cut 1024 15+point 4 cut 1024 16)/2)
    have hp : middlePayment 15 = (626125378144:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 15+point 4 cut 1024 16)/2 = (84385443:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84385443:ℝ)/21094400) = (33971200:ℝ)/21604701 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84385443:ℝ)/21094400)-4 = (7843:ℝ)/21094400 by norm_num]
    exact paid_middle_15
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_000
