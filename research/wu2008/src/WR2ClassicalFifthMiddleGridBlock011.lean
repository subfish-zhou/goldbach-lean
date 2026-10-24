import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints011
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_011 (j : Fin 16) : middlePayment (16*11+j.val) ≤
    middleValue ((point 4 cut 1024 (16*11+j.val)+point 4 cut 1024 (16*11+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 176 ≤ middleValue ((point 4 cut 1024 176+point 4 cut 1024 177)/2)
    have hp : middlePayment 176 = (632408194353:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 176+point 4 cut 1024 177)/2 = (84466909:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84466909:ℝ)/21094400) = (6794240:ℝ)/4304647 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84466909:ℝ)/21094400)-4 = (89309:ℝ)/21094400 by norm_num]
    exact paid_middle_176
  · change middlePayment 177 ≤ middleValue ((point 4 cut 1024 177+point 4 cut 1024 178)/2)
    have hp : middlePayment 177 = (632447340551:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 177+point 4 cut 1024 178)/2 = (16893483:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16893483:ℝ)/4218880) = (33971200:ℝ)/21522729 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16893483:ℝ)/4218880)-4 = (17963:ℝ)/4218880 by norm_num]
    exact paid_middle_177
  · change middlePayment 178 ≤ middleValue ((point 4 cut 1024 178+point 4 cut 1024 179)/2)
    have hp : middlePayment 178 = (632486488265:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 178+point 4 cut 1024 179)/2 = (84467921:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84467921:ℝ)/21094400) = (33971200:ℝ)/21522223 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84467921:ℝ)/21094400)-4 = (90321:ℝ)/21094400 by norm_num]
    exact paid_middle_178
  · change middlePayment 179 ≤ middleValue ((point 4 cut 1024 179+point 4 cut 1024 180)/2)
    have hp : middlePayment 179 = (632525637496:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 179+point 4 cut 1024 180)/2 = (84468427:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84468427:ℝ)/21094400) = (33971200:ℝ)/21521717 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84468427:ℝ)/21094400)-4 = (90827:ℝ)/21094400 by norm_num]
    exact paid_middle_179
  · change middlePayment 180 ≤ middleValue ((point 4 cut 1024 180+point 4 cut 1024 181)/2)
    have hp : middlePayment 180 = (632564788243:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 180+point 4 cut 1024 181)/2 = (84468933:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84468933:ℝ)/21094400) = (33971200:ℝ)/21521211 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84468933:ℝ)/21094400)-4 = (91333:ℝ)/21094400 by norm_num]
    exact paid_middle_180
  · change middlePayment 181 ≤ middleValue ((point 4 cut 1024 181+point 4 cut 1024 182)/2)
    have hp : middlePayment 181 = (632603940507:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 181+point 4 cut 1024 182)/2 = (84469439:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84469439:ℝ)/21094400) = (6794240:ℝ)/4304141 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84469439:ℝ)/21094400)-4 = (91839:ℝ)/21094400 by norm_num]
    exact paid_middle_181
  · change middlePayment 182 ≤ middleValue ((point 4 cut 1024 182+point 4 cut 1024 183)/2)
    have hp : middlePayment 182 = (632643094288:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 182+point 4 cut 1024 183)/2 = (16893989:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16893989:ℝ)/4218880) = (33971200:ℝ)/21520199 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16893989:ℝ)/4218880)-4 = (18469:ℝ)/4218880 by norm_num]
    exact paid_middle_182
  · change middlePayment 183 ≤ middleValue ((point 4 cut 1024 183+point 4 cut 1024 184)/2)
    have hp : middlePayment 183 = (632682249585:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 183+point 4 cut 1024 184)/2 = (84470451:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84470451:ℝ)/21094400) = (33971200:ℝ)/21519693 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84470451:ℝ)/21094400)-4 = (92851:ℝ)/21094400 by norm_num]
    exact paid_middle_183
  · change middlePayment 184 ≤ middleValue ((point 4 cut 1024 184+point 4 cut 1024 185)/2)
    have hp : middlePayment 184 = (632721406400:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 184+point 4 cut 1024 185)/2 = (84470957:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84470957:ℝ)/21094400) = (33971200:ℝ)/21519187 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84470957:ℝ)/21094400)-4 = (93357:ℝ)/21094400 by norm_num]
    exact paid_middle_184
  · change middlePayment 185 ≤ middleValue ((point 4 cut 1024 185+point 4 cut 1024 186)/2)
    have hp : middlePayment 185 = (632760564731:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 185+point 4 cut 1024 186)/2 = (84471463:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84471463:ℝ)/21094400) = (33971200:ℝ)/21518681 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84471463:ℝ)/21094400)-4 = (93863:ℝ)/21094400 by norm_num]
    exact paid_middle_185
  · change middlePayment 186 ≤ middleValue ((point 4 cut 1024 186+point 4 cut 1024 187)/2)
    have hp : middlePayment 186 = (632799724579:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 186+point 4 cut 1024 187)/2 = (84471969:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84471969:ℝ)/21094400) = (1358848:ℝ)/860727 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84471969:ℝ)/21094400)-4 = (94369:ℝ)/21094400 by norm_num]
    exact paid_middle_186
  · change middlePayment 187 ≤ middleValue ((point 4 cut 1024 187+point 4 cut 1024 188)/2)
    have hp : middlePayment 187 = (632838885944:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 187+point 4 cut 1024 188)/2 = (3378899:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3378899:ℝ)/843776) = (33971200:ℝ)/21517669 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3378899:ℝ)/843776)-4 = (3795:ℝ)/843776 by norm_num]
    exact paid_middle_187
  · change middlePayment 188 ≤ middleValue ((point 4 cut 1024 188+point 4 cut 1024 189)/2)
    have hp : middlePayment 188 = (632878048827:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 188+point 4 cut 1024 189)/2 = (84472981:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84472981:ℝ)/21094400) = (33971200:ℝ)/21517163 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84472981:ℝ)/21094400)-4 = (95381:ℝ)/21094400 by norm_num]
    exact paid_middle_188
  · change middlePayment 189 ≤ middleValue ((point 4 cut 1024 189+point 4 cut 1024 190)/2)
    have hp : middlePayment 189 = (632917213227:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 189+point 4 cut 1024 190)/2 = (84473487:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84473487:ℝ)/21094400) = (33971200:ℝ)/21516657 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84473487:ℝ)/21094400)-4 = (95887:ℝ)/21094400 by norm_num]
    exact paid_middle_189
  · change middlePayment 190 ≤ middleValue ((point 4 cut 1024 190+point 4 cut 1024 191)/2)
    have hp : middlePayment 190 = (632956379144:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 190+point 4 cut 1024 191)/2 = (84473993:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84473993:ℝ)/21094400) = (33971200:ℝ)/21516151 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84473993:ℝ)/21094400)-4 = (96393:ℝ)/21094400 by norm_num]
    exact paid_middle_190
  · change middlePayment 191 ≤ middleValue ((point 4 cut 1024 191+point 4 cut 1024 192)/2)
    have hp : middlePayment 191 = (632995546578:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 191+point 4 cut 1024 192)/2 = (84474499:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84474499:ℝ)/21094400) = (6794240:ℝ)/4303129 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84474499:ℝ)/21094400)-4 = (96899:ℝ)/21094400 by norm_num]
    exact paid_middle_191
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_011
