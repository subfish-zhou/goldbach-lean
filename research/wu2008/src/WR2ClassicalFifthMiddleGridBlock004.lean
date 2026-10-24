import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints004
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_004 (j : Fin 16) : middlePayment (16*4+j.val) ≤
    middleValue ((point 4 cut 1024 (16*4+j.val)+point 4 cut 1024 (16*4+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 64 ≤ middleValue ((point 4 cut 1024 64+point 4 cut 1024 65)/2)
    have hp : middlePayment 64 = (628033397718:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 64+point 4 cut 1024 65)/2 = (84410237:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84410237:ℝ)/21094400) = (33971200:ℝ)/21579907 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84410237:ℝ)/21094400)-4 = (32637:ℝ)/21094400 by norm_num]
    exact paid_middle_64
  · change middlePayment 65 ≤ middleValue ((point 4 cut 1024 65+point 4 cut 1024 66)/2)
    have hp : middlePayment 65 = (628072374559:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 65+point 4 cut 1024 66)/2 = (84410743:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84410743:ℝ)/21094400) = (33971200:ℝ)/21579401 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84410743:ℝ)/21094400)-4 = (33143:ℝ)/21094400 by norm_num]
    exact paid_middle_65
  · change middlePayment 66 ≤ middleValue ((point 4 cut 1024 66+point 4 cut 1024 67)/2)
    have hp : middlePayment 66 = (628111352908:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 66+point 4 cut 1024 67)/2 = (84411249:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84411249:ℝ)/21094400) = (6794240:ℝ)/4315779 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84411249:ℝ)/21094400)-4 = (33649:ℝ)/21094400 by norm_num]
    exact paid_middle_66
  · change middlePayment 67 ≤ middleValue ((point 4 cut 1024 67+point 4 cut 1024 68)/2)
    have hp : middlePayment 67 = (628150332765:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 67+point 4 cut 1024 68)/2 = (16882351:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16882351:ℝ)/4218880) = (33971200:ℝ)/21578389 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16882351:ℝ)/4218880)-4 = (6831:ℝ)/4218880 by norm_num]
    exact paid_middle_67
  · change middlePayment 68 ≤ middleValue ((point 4 cut 1024 68+point 4 cut 1024 69)/2)
    have hp : middlePayment 68 = (628189314130:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 68+point 4 cut 1024 69)/2 = (84412261:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84412261:ℝ)/21094400) = (33971200:ℝ)/21577883 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84412261:ℝ)/21094400)-4 = (34661:ℝ)/21094400 by norm_num]
    exact paid_middle_68
  · change middlePayment 69 ≤ middleValue ((point 4 cut 1024 69+point 4 cut 1024 70)/2)
    have hp : middlePayment 69 = (628228297003:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 69+point 4 cut 1024 70)/2 = (84412767:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84412767:ℝ)/21094400) = (33971200:ℝ)/21577377 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84412767:ℝ)/21094400)-4 = (35167:ℝ)/21094400 by norm_num]
    exact paid_middle_69
  · change middlePayment 70 ≤ middleValue ((point 4 cut 1024 70+point 4 cut 1024 71)/2)
    have hp : middlePayment 70 = (628267281384:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 70+point 4 cut 1024 71)/2 = (84413273:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84413273:ℝ)/21094400) = (33971200:ℝ)/21576871 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84413273:ℝ)/21094400)-4 = (35673:ℝ)/21094400 by norm_num]
    exact paid_middle_70
  · change middlePayment 71 ≤ middleValue ((point 4 cut 1024 71+point 4 cut 1024 72)/2)
    have hp : middlePayment 71 = (628306267274:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 71+point 4 cut 1024 72)/2 = (84413779:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84413779:ℝ)/21094400) = (6794240:ℝ)/4315273 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84413779:ℝ)/21094400)-4 = (36179:ℝ)/21094400 by norm_num]
    exact paid_middle_71
  · change middlePayment 72 ≤ middleValue ((point 4 cut 1024 72+point 4 cut 1024 73)/2)
    have hp : middlePayment 72 = (628345254672:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 72+point 4 cut 1024 73)/2 = (16882857:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16882857:ℝ)/4218880) = (33971200:ℝ)/21575859 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16882857:ℝ)/4218880)-4 = (7337:ℝ)/4218880 by norm_num]
    exact paid_middle_72
  · change middlePayment 73 ≤ middleValue ((point 4 cut 1024 73+point 4 cut 1024 74)/2)
    have hp : middlePayment 73 = (628384243578:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 73+point 4 cut 1024 74)/2 = (84414791:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84414791:ℝ)/21094400) = (33971200:ℝ)/21575353 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84414791:ℝ)/21094400)-4 = (37191:ℝ)/21094400 by norm_num]
    exact paid_middle_73
  · change middlePayment 74 ≤ middleValue ((point 4 cut 1024 74+point 4 cut 1024 75)/2)
    have hp : middlePayment 74 = (628423233993:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 74+point 4 cut 1024 75)/2 = (84415297:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84415297:ℝ)/21094400) = (33971200:ℝ)/21574847 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84415297:ℝ)/21094400)-4 = (37697:ℝ)/21094400 by norm_num]
    exact paid_middle_74
  · change middlePayment 75 ≤ middleValue ((point 4 cut 1024 75+point 4 cut 1024 76)/2)
    have hp : middlePayment 75 = (628462225916:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 75+point 4 cut 1024 76)/2 = (84415803:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84415803:ℝ)/21094400) = (33971200:ℝ)/21574341 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84415803:ℝ)/21094400)-4 = (38203:ℝ)/21094400 by norm_num]
    exact paid_middle_75
  · change middlePayment 76 ≤ middleValue ((point 4 cut 1024 76+point 4 cut 1024 77)/2)
    have hp : middlePayment 76 = (628501219349:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 76+point 4 cut 1024 77)/2 = (84416309:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84416309:ℝ)/21094400) = (6794240:ℝ)/4314767 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84416309:ℝ)/21094400)-4 = (38709:ℝ)/21094400 by norm_num]
    exact paid_middle_76
  · change middlePayment 77 ≤ middleValue ((point 4 cut 1024 77+point 4 cut 1024 78)/2)
    have hp : middlePayment 77 = (628540214290:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 77+point 4 cut 1024 78)/2 = (16883363:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16883363:ℝ)/4218880) = (33971200:ℝ)/21573329 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16883363:ℝ)/4218880)-4 = (7843:ℝ)/4218880 by norm_num]
    exact paid_middle_77
  · change middlePayment 78 ≤ middleValue ((point 4 cut 1024 78+point 4 cut 1024 79)/2)
    have hp : middlePayment 78 = (628579210739:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 78+point 4 cut 1024 79)/2 = (84417321:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84417321:ℝ)/21094400) = (33971200:ℝ)/21572823 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84417321:ℝ)/21094400)-4 = (39721:ℝ)/21094400 by norm_num]
    exact paid_middle_78
  · change middlePayment 79 ≤ middleValue ((point 4 cut 1024 79+point 4 cut 1024 80)/2)
    have hp : middlePayment 79 = (628618208698:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 79+point 4 cut 1024 80)/2 = (84417827:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84417827:ℝ)/21094400) = (33971200:ℝ)/21572317 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84417827:ℝ)/21094400)-4 = (40227:ℝ)/21094400 by norm_num]
    exact paid_middle_79
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_004
