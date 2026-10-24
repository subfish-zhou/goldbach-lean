import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints009
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_009 (j : Fin 16) : middlePayment (16*9+j.val) ≤
    middleValue ((point 4 cut 1024 (16*9+j.val)+point 4 cut 1024 (16*9+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 144 ≤ middleValue ((point 4 cut 1024 144+point 4 cut 1024 145)/2)
    have hp : middlePayment 144 = (631156316224:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 144+point 4 cut 1024 145)/2 = (84450717:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84450717:ℝ)/21094400) = (33971200:ℝ)/21539427 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84450717:ℝ)/21094400)-4 = (73117:ℝ)/21094400 by norm_num]
    exact paid_middle_144
  · change middlePayment 145 ≤ middleValue ((point 4 cut 1024 145+point 4 cut 1024 146)/2)
    have hp : middlePayment 145 = (631195413938:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 145+point 4 cut 1024 146)/2 = (84451223:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84451223:ℝ)/21094400) = (33971200:ℝ)/21538921 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84451223:ℝ)/21094400)-4 = (73623:ℝ)/21094400 by norm_num]
    exact paid_middle_145
  · change middlePayment 146 ≤ middleValue ((point 4 cut 1024 146+point 4 cut 1024 147)/2)
    have hp : middlePayment 146 = (631234513165:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 146+point 4 cut 1024 147)/2 = (84451729:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84451729:ℝ)/21094400) = (6794240:ℝ)/4307683 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84451729:ℝ)/21094400)-4 = (74129:ℝ)/21094400 by norm_num]
    exact paid_middle_146
  · change middlePayment 147 ≤ middleValue ((point 4 cut 1024 147+point 4 cut 1024 148)/2)
    have hp : middlePayment 147 = (631273613906:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 147+point 4 cut 1024 148)/2 = (16890447:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16890447:ℝ)/4218880) = (33971200:ℝ)/21537909 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16890447:ℝ)/4218880)-4 = (14927:ℝ)/4218880 by norm_num]
    exact paid_middle_147
  · change middlePayment 148 ≤ middleValue ((point 4 cut 1024 148+point 4 cut 1024 149)/2)
    have hp : middlePayment 148 = (631312716162:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 148+point 4 cut 1024 149)/2 = (84452741:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84452741:ℝ)/21094400) = (33971200:ℝ)/21537403 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84452741:ℝ)/21094400)-4 = (75141:ℝ)/21094400 by norm_num]
    exact paid_middle_148
  · change middlePayment 149 ≤ middleValue ((point 4 cut 1024 149+point 4 cut 1024 150)/2)
    have hp : middlePayment 149 = (631351819931:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 149+point 4 cut 1024 150)/2 = (84453247:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84453247:ℝ)/21094400) = (33971200:ℝ)/21536897 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84453247:ℝ)/21094400)-4 = (75647:ℝ)/21094400 by norm_num]
    exact paid_middle_149
  · change middlePayment 150 ≤ middleValue ((point 4 cut 1024 150+point 4 cut 1024 151)/2)
    have hp : middlePayment 150 = (631390925215:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 150+point 4 cut 1024 151)/2 = (84453753:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84453753:ℝ)/21094400) = (33971200:ℝ)/21536391 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84453753:ℝ)/21094400)-4 = (76153:ℝ)/21094400 by norm_num]
    exact paid_middle_150
  · change middlePayment 151 ≤ middleValue ((point 4 cut 1024 151+point 4 cut 1024 152)/2)
    have hp : middlePayment 151 = (631430032013:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 151+point 4 cut 1024 152)/2 = (84454259:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84454259:ℝ)/21094400) = (6794240:ℝ)/4307177 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84454259:ℝ)/21094400)-4 = (76659:ℝ)/21094400 by norm_num]
    exact paid_middle_151
  · change middlePayment 152 ≤ middleValue ((point 4 cut 1024 152+point 4 cut 1024 153)/2)
    have hp : middlePayment 152 = (631469140326:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 152+point 4 cut 1024 153)/2 = (16890953:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16890953:ℝ)/4218880) = (33971200:ℝ)/21535379 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16890953:ℝ)/4218880)-4 = (15433:ℝ)/4218880 by norm_num]
    exact paid_middle_152
  · change middlePayment 153 ≤ middleValue ((point 4 cut 1024 153+point 4 cut 1024 154)/2)
    have hp : middlePayment 153 = (631508250153:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 153+point 4 cut 1024 154)/2 = (84455271:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84455271:ℝ)/21094400) = (33971200:ℝ)/21534873 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84455271:ℝ)/21094400)-4 = (77671:ℝ)/21094400 by norm_num]
    exact paid_middle_153
  · change middlePayment 154 ≤ middleValue ((point 4 cut 1024 154+point 4 cut 1024 155)/2)
    have hp : middlePayment 154 = (631547361495:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 154+point 4 cut 1024 155)/2 = (819959:ℝ)/204800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((819959:ℝ)/204800) = (33971200:ℝ)/21534367 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((819959:ℝ)/204800)-4 = (759:ℝ)/204800 by norm_num]
    exact paid_middle_154
  · change middlePayment 155 ≤ middleValue ((point 4 cut 1024 155+point 4 cut 1024 156)/2)
    have hp : middlePayment 155 = (631586474351:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 155+point 4 cut 1024 156)/2 = (84456283:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84456283:ℝ)/21094400) = (33971200:ℝ)/21533861 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84456283:ℝ)/21094400)-4 = (78683:ℝ)/21094400 by norm_num]
    exact paid_middle_155
  · change middlePayment 156 ≤ middleValue ((point 4 cut 1024 156+point 4 cut 1024 157)/2)
    have hp : middlePayment 156 = (631625588722:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 156+point 4 cut 1024 157)/2 = (84456789:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84456789:ℝ)/21094400) = (6794240:ℝ)/4306671 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84456789:ℝ)/21094400)-4 = (79189:ℝ)/21094400 by norm_num]
    exact paid_middle_156
  · change middlePayment 157 ≤ middleValue ((point 4 cut 1024 157+point 4 cut 1024 158)/2)
    have hp : middlePayment 157 = (631664704608:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 157+point 4 cut 1024 158)/2 = (16891459:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16891459:ℝ)/4218880) = (33971200:ℝ)/21532849 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16891459:ℝ)/4218880)-4 = (15939:ℝ)/4218880 by norm_num]
    exact paid_middle_157
  · change middlePayment 158 ≤ middleValue ((point 4 cut 1024 158+point 4 cut 1024 159)/2)
    have hp : middlePayment 158 = (631703822009:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 158+point 4 cut 1024 159)/2 = (84457801:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84457801:ℝ)/21094400) = (33971200:ℝ)/21532343 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84457801:ℝ)/21094400)-4 = (80201:ℝ)/21094400 by norm_num]
    exact paid_middle_158
  · change middlePayment 159 ≤ middleValue ((point 4 cut 1024 159+point 4 cut 1024 160)/2)
    have hp : middlePayment 159 = (631742940924:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 159+point 4 cut 1024 160)/2 = (84458307:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84458307:ℝ)/21094400) = (33971200:ℝ)/21531837 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84458307:ℝ)/21094400)-4 = (80707:ℝ)/21094400 by norm_num]
    exact paid_middle_159
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_009
