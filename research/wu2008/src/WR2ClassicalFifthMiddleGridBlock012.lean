import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints012
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_012 (j : Fin 16) : middlePayment (16*12+j.val) ≤
    middleValue ((point 4 cut 1024 (16*12+j.val)+point 4 cut 1024 (16*12+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 192 ≤ middleValue ((point 4 cut 1024 192+point 4 cut 1024 193)/2)
    have hp : middlePayment 192 = (633034715530:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 192+point 4 cut 1024 193)/2 = (16895001:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16895001:ℝ)/4218880) = (33971200:ℝ)/21515139 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16895001:ℝ)/4218880)-4 = (19481:ℝ)/4218880 by norm_num]
    exact paid_middle_192
  · change middlePayment 193 ≤ middleValue ((point 4 cut 1024 193+point 4 cut 1024 194)/2)
    have hp : middlePayment 193 = (633073885999:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 193+point 4 cut 1024 194)/2 = (84475511:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84475511:ℝ)/21094400) = (33971200:ℝ)/21514633 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84475511:ℝ)/21094400)-4 = (97911:ℝ)/21094400 by norm_num]
    exact paid_middle_193
  · change middlePayment 194 ≤ middleValue ((point 4 cut 1024 194+point 4 cut 1024 195)/2)
    have hp : middlePayment 194 = (633113057986:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 194+point 4 cut 1024 195)/2 = (84476017:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84476017:ℝ)/21094400) = (33971200:ℝ)/21514127 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84476017:ℝ)/21094400)-4 = (98417:ℝ)/21094400 by norm_num]
    exact paid_middle_194
  · change middlePayment 195 ≤ middleValue ((point 4 cut 1024 195+point 4 cut 1024 196)/2)
    have hp : middlePayment 195 = (633152231491:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 195+point 4 cut 1024 196)/2 = (84476523:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84476523:ℝ)/21094400) = (33971200:ℝ)/21513621 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84476523:ℝ)/21094400)-4 = (98923:ℝ)/21094400 by norm_num]
    exact paid_middle_195
  · change middlePayment 196 ≤ middleValue ((point 4 cut 1024 196+point 4 cut 1024 197)/2)
    have hp : middlePayment 196 = (633191406513:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 196+point 4 cut 1024 197)/2 = (84477029:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84477029:ℝ)/21094400) = (6794240:ℝ)/4302623 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84477029:ℝ)/21094400)-4 = (99429:ℝ)/21094400 by norm_num]
    exact paid_middle_196
  · change middlePayment 197 ≤ middleValue ((point 4 cut 1024 197+point 4 cut 1024 198)/2)
    have hp : middlePayment 197 = (633230583054:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 197+point 4 cut 1024 198)/2 = (16895507:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16895507:ℝ)/4218880) = (33971200:ℝ)/21512609 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16895507:ℝ)/4218880)-4 = (19987:ℝ)/4218880 by norm_num]
    exact paid_middle_197
  · change middlePayment 198 ≤ middleValue ((point 4 cut 1024 198+point 4 cut 1024 199)/2)
    have hp : middlePayment 198 = (633269761112:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 198+point 4 cut 1024 199)/2 = (84478041:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84478041:ℝ)/21094400) = (33971200:ℝ)/21512103 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84478041:ℝ)/21094400)-4 = (100441:ℝ)/21094400 by norm_num]
    exact paid_middle_198
  · change middlePayment 199 ≤ middleValue ((point 4 cut 1024 199+point 4 cut 1024 200)/2)
    have hp : middlePayment 199 = (633308940688:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 199+point 4 cut 1024 200)/2 = (84478547:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84478547:ℝ)/21094400) = (33971200:ℝ)/21511597 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84478547:ℝ)/21094400)-4 = (100947:ℝ)/21094400 by norm_num]
    exact paid_middle_199
  · change middlePayment 200 ≤ middleValue ((point 4 cut 1024 200+point 4 cut 1024 201)/2)
    have hp : middlePayment 200 = (633348121782:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 200+point 4 cut 1024 201)/2 = (84479053:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84479053:ℝ)/21094400) = (33971200:ℝ)/21511091 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84479053:ℝ)/21094400)-4 = (101453:ℝ)/21094400 by norm_num]
    exact paid_middle_200
  · change middlePayment 201 ≤ middleValue ((point 4 cut 1024 201+point 4 cut 1024 202)/2)
    have hp : middlePayment 201 = (633387304395:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 201+point 4 cut 1024 202)/2 = (84479559:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84479559:ℝ)/21094400) = (6794240:ℝ)/4302117 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84479559:ℝ)/21094400)-4 = (101959:ℝ)/21094400 by norm_num]
    exact paid_middle_201
  · change middlePayment 202 ≤ middleValue ((point 4 cut 1024 202+point 4 cut 1024 203)/2)
    have hp : middlePayment 202 = (633426488526:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 202+point 4 cut 1024 203)/2 = (16896013:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16896013:ℝ)/4218880) = (33971200:ℝ)/21510079 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16896013:ℝ)/4218880)-4 = (20493:ℝ)/4218880 by norm_num]
    exact paid_middle_202
  · change middlePayment 203 ≤ middleValue ((point 4 cut 1024 203+point 4 cut 1024 204)/2)
    have hp : middlePayment 203 = (633465674175:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 203+point 4 cut 1024 204)/2 = (84480571:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84480571:ℝ)/21094400) = (33971200:ℝ)/21509573 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84480571:ℝ)/21094400)-4 = (102971:ℝ)/21094400 by norm_num]
    exact paid_middle_203
  · change middlePayment 204 ≤ middleValue ((point 4 cut 1024 204+point 4 cut 1024 205)/2)
    have hp : middlePayment 204 = (633504861342:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 204+point 4 cut 1024 205)/2 = (84481077:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84481077:ℝ)/21094400) = (33971200:ℝ)/21509067 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84481077:ℝ)/21094400)-4 = (103477:ℝ)/21094400 by norm_num]
    exact paid_middle_204
  · change middlePayment 205 ≤ middleValue ((point 4 cut 1024 205+point 4 cut 1024 206)/2)
    have hp : middlePayment 205 = (633544050028:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 205+point 4 cut 1024 206)/2 = (84481583:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84481583:ℝ)/21094400) = (33971200:ℝ)/21508561 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84481583:ℝ)/21094400)-4 = (103983:ℝ)/21094400 by norm_num]
    exact paid_middle_205
  · change middlePayment 206 ≤ middleValue ((point 4 cut 1024 206+point 4 cut 1024 207)/2)
    have hp : middlePayment 206 = (633583240232:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 206+point 4 cut 1024 207)/2 = (84482089:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84482089:ℝ)/21094400) = (6794240:ℝ)/4301611 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84482089:ℝ)/21094400)-4 = (104489:ℝ)/21094400 by norm_num]
    exact paid_middle_206
  · change middlePayment 207 ≤ middleValue ((point 4 cut 1024 207+point 4 cut 1024 208)/2)
    have hp : middlePayment 207 = (633622431955:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 207+point 4 cut 1024 208)/2 = (16896519:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16896519:ℝ)/4218880) = (33971200:ℝ)/21507549 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16896519:ℝ)/4218880)-4 = (20999:ℝ)/4218880 by norm_num]
    exact paid_middle_207
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_012
