import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints010
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_010 (j : Fin 16) : middlePayment (16*10+j.val) ≤
    middleValue ((point 4 cut 1024 (16*10+j.val)+point 4 cut 1024 (16*10+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 160 ≤ middleValue ((point 4 cut 1024 160+point 4 cut 1024 161)/2)
    have hp : middlePayment 160 = (631782061355:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 160+point 4 cut 1024 161)/2 = (84458813:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84458813:ℝ)/21094400) = (33971200:ℝ)/21531331 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84458813:ℝ)/21094400)-4 = (81213:ℝ)/21094400 by norm_num]
    exact paid_middle_160
  · change middlePayment 161 ≤ middleValue ((point 4 cut 1024 161+point 4 cut 1024 162)/2)
    have hp : middlePayment 161 = (631821183301:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 161+point 4 cut 1024 162)/2 = (84459319:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84459319:ℝ)/21094400) = (1358848:ℝ)/861233 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84459319:ℝ)/21094400)-4 = (81719:ℝ)/21094400 by norm_num]
    exact paid_middle_161
  · change middlePayment 162 ≤ middleValue ((point 4 cut 1024 162+point 4 cut 1024 163)/2)
    have hp : middlePayment 162 = (631860306762:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 162+point 4 cut 1024 163)/2 = (3378393:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3378393:ℝ)/843776) = (33971200:ℝ)/21530319 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3378393:ℝ)/843776)-4 = (3289:ℝ)/843776 by norm_num]
    exact paid_middle_162
  · change middlePayment 163 ≤ middleValue ((point 4 cut 1024 163+point 4 cut 1024 164)/2)
    have hp : middlePayment 163 = (631899431738:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 163+point 4 cut 1024 164)/2 = (84460331:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84460331:ℝ)/21094400) = (33971200:ℝ)/21529813 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84460331:ℝ)/21094400)-4 = (82731:ℝ)/21094400 by norm_num]
    exact paid_middle_163
  · change middlePayment 164 ≤ middleValue ((point 4 cut 1024 164+point 4 cut 1024 165)/2)
    have hp : middlePayment 164 = (631938558230:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 164+point 4 cut 1024 165)/2 = (84460837:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84460837:ℝ)/21094400) = (33971200:ℝ)/21529307 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84460837:ℝ)/21094400)-4 = (83237:ℝ)/21094400 by norm_num]
    exact paid_middle_164
  · change middlePayment 165 ≤ middleValue ((point 4 cut 1024 165+point 4 cut 1024 166)/2)
    have hp : middlePayment 165 = (631977686237:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 165+point 4 cut 1024 166)/2 = (84461343:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84461343:ℝ)/21094400) = (33971200:ℝ)/21528801 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84461343:ℝ)/21094400)-4 = (83743:ℝ)/21094400 by norm_num]
    exact paid_middle_165
  · change middlePayment 166 ≤ middleValue ((point 4 cut 1024 166+point 4 cut 1024 167)/2)
    have hp : middlePayment 166 = (632016815759:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 166+point 4 cut 1024 167)/2 = (84461849:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84461849:ℝ)/21094400) = (6794240:ℝ)/4305659 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84461849:ℝ)/21094400)-4 = (84249:ℝ)/21094400 by norm_num]
    exact paid_middle_166
  · change middlePayment 167 ≤ middleValue ((point 4 cut 1024 167+point 4 cut 1024 168)/2)
    have hp : middlePayment 167 = (632055946798:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 167+point 4 cut 1024 168)/2 = (16892471:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16892471:ℝ)/4218880) = (33971200:ℝ)/21527789 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16892471:ℝ)/4218880)-4 = (16951:ℝ)/4218880 by norm_num]
    exact paid_middle_167
  · change middlePayment 168 ≤ middleValue ((point 4 cut 1024 168+point 4 cut 1024 169)/2)
    have hp : middlePayment 168 = (632095079351:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 168+point 4 cut 1024 169)/2 = (84462861:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84462861:ℝ)/21094400) = (33971200:ℝ)/21527283 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84462861:ℝ)/21094400)-4 = (85261:ℝ)/21094400 by norm_num]
    exact paid_middle_168
  · change middlePayment 169 ≤ middleValue ((point 4 cut 1024 169+point 4 cut 1024 170)/2)
    have hp : middlePayment 169 = (632134213421:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 169+point 4 cut 1024 170)/2 = (84463367:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84463367:ℝ)/21094400) = (33971200:ℝ)/21526777 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84463367:ℝ)/21094400)-4 = (85767:ℝ)/21094400 by norm_num]
    exact paid_middle_169
  · change middlePayment 170 ≤ middleValue ((point 4 cut 1024 170+point 4 cut 1024 171)/2)
    have hp : middlePayment 170 = (632173349006:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 170+point 4 cut 1024 171)/2 = (84463873:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84463873:ℝ)/21094400) = (33971200:ℝ)/21526271 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84463873:ℝ)/21094400)-4 = (86273:ℝ)/21094400 by norm_num]
    exact paid_middle_170
  · change middlePayment 171 ≤ middleValue ((point 4 cut 1024 171+point 4 cut 1024 172)/2)
    have hp : middlePayment 171 = (632212486107:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 171+point 4 cut 1024 172)/2 = (84464379:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84464379:ℝ)/21094400) = (6794240:ℝ)/4305153 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84464379:ℝ)/21094400)-4 = (86779:ℝ)/21094400 by norm_num]
    exact paid_middle_171
  · change middlePayment 172 ≤ middleValue ((point 4 cut 1024 172+point 4 cut 1024 173)/2)
    have hp : middlePayment 172 = (632251624724:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 172+point 4 cut 1024 173)/2 = (16892977:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16892977:ℝ)/4218880) = (33971200:ℝ)/21525259 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16892977:ℝ)/4218880)-4 = (17457:ℝ)/4218880 by norm_num]
    exact paid_middle_172
  · change middlePayment 173 ≤ middleValue ((point 4 cut 1024 173+point 4 cut 1024 174)/2)
    have hp : middlePayment 173 = (632290764857:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 173+point 4 cut 1024 174)/2 = (84465391:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84465391:ℝ)/21094400) = (33971200:ℝ)/21524753 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84465391:ℝ)/21094400)-4 = (87791:ℝ)/21094400 by norm_num]
    exact paid_middle_173
  · change middlePayment 174 ≤ middleValue ((point 4 cut 1024 174+point 4 cut 1024 175)/2)
    have hp : middlePayment 174 = (632329906506:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 174+point 4 cut 1024 175)/2 = (84465897:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84465897:ℝ)/21094400) = (33971200:ℝ)/21524247 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84465897:ℝ)/21094400)-4 = (88297:ℝ)/21094400 by norm_num]
    exact paid_middle_174
  · change middlePayment 175 ≤ middleValue ((point 4 cut 1024 175+point 4 cut 1024 176)/2)
    have hp : middlePayment 175 = (632369049672:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 175+point 4 cut 1024 176)/2 = (84466403:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84466403:ℝ)/21094400) = (33971200:ℝ)/21523741 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84466403:ℝ)/21094400)-4 = (88803:ℝ)/21094400 by norm_num]
    exact paid_middle_175
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_010
