import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints019
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_019 (j : Fin 16) : middlePayment (16*19+j.val) ≤
    middleValue ((point 4 cut 1024 (16*19+j.val)+point 4 cut 1024 (16*19+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 304 ≤ middleValue ((point 4 cut 1024 304+point 4 cut 1024 305)/2)
    have hp : middlePayment 304 = (637431258979:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 304+point 4 cut 1024 305)/2 = (84531677:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84531677:ℝ)/21094400) = (33971200:ℝ)/21458467 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84531677:ℝ)/21094400)-4 = (154077:ℝ)/21094400 by norm_num]
    exact paid_middle_304
  · change middlePayment 305 ≤ middleValue ((point 4 cut 1024 305+point 4 cut 1024 306)/2)
    have hp : middlePayment 305 = (637470599895:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 305+point 4 cut 1024 306)/2 = (84532183:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84532183:ℝ)/21094400) = (33971200:ℝ)/21457961 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84532183:ℝ)/21094400)-4 = (154583:ℝ)/21094400 by norm_num]
    exact paid_middle_305
  · change middlePayment 306 ≤ middleValue ((point 4 cut 1024 306+point 4 cut 1024 307)/2)
    have hp : middlePayment 306 = (637509942338:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 306+point 4 cut 1024 307)/2 = (84532689:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84532689:ℝ)/21094400) = (6794240:ℝ)/4291491 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84532689:ℝ)/21094400)-4 = (155089:ℝ)/21094400 by norm_num]
    exact paid_middle_306
  · change middlePayment 307 ≤ middleValue ((point 4 cut 1024 307+point 4 cut 1024 308)/2)
    have hp : middlePayment 307 = (637549286307:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 307+point 4 cut 1024 308)/2 = (16906639:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16906639:ℝ)/4218880) = (33971200:ℝ)/21456949 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16906639:ℝ)/4218880)-4 = (31119:ℝ)/4218880 by norm_num]
    exact paid_middle_307
  · change middlePayment 308 ≤ middleValue ((point 4 cut 1024 308+point 4 cut 1024 309)/2)
    have hp : middlePayment 308 = (637588631802:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 308+point 4 cut 1024 309)/2 = (84533701:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84533701:ℝ)/21094400) = (33971200:ℝ)/21456443 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84533701:ℝ)/21094400)-4 = (156101:ℝ)/21094400 by norm_num]
    exact paid_middle_308
  · change middlePayment 309 ≤ middleValue ((point 4 cut 1024 309+point 4 cut 1024 310)/2)
    have hp : middlePayment 309 = (637627978824:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 309+point 4 cut 1024 310)/2 = (84534207:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84534207:ℝ)/21094400) = (33971200:ℝ)/21455937 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84534207:ℝ)/21094400)-4 = (156607:ℝ)/21094400 by norm_num]
    exact paid_middle_309
  · change middlePayment 310 ≤ middleValue ((point 4 cut 1024 310+point 4 cut 1024 311)/2)
    have hp : middlePayment 310 = (637667327373:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 310+point 4 cut 1024 311)/2 = (84534713:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84534713:ℝ)/21094400) = (33971200:ℝ)/21455431 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84534713:ℝ)/21094400)-4 = (157113:ℝ)/21094400 by norm_num]
    exact paid_middle_310
  · change middlePayment 311 ≤ middleValue ((point 4 cut 1024 311+point 4 cut 1024 312)/2)
    have hp : middlePayment 311 = (637706677447:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 311+point 4 cut 1024 312)/2 = (84535219:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84535219:ℝ)/21094400) = (1358848:ℝ)/858197 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84535219:ℝ)/21094400)-4 = (157619:ℝ)/21094400 by norm_num]
    exact paid_middle_311
  · change middlePayment 312 ≤ middleValue ((point 4 cut 1024 312+point 4 cut 1024 313)/2)
    have hp : middlePayment 312 = (637746029049:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 312+point 4 cut 1024 313)/2 = (3381429:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3381429:ℝ)/843776) = (33971200:ℝ)/21454419 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3381429:ℝ)/843776)-4 = (6325:ℝ)/843776 by norm_num]
    exact paid_middle_312
  · change middlePayment 313 ≤ middleValue ((point 4 cut 1024 313+point 4 cut 1024 314)/2)
    have hp : middlePayment 313 = (637785382177:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 313+point 4 cut 1024 314)/2 = (84536231:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84536231:ℝ)/21094400) = (33971200:ℝ)/21453913 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84536231:ℝ)/21094400)-4 = (158631:ℝ)/21094400 by norm_num]
    exact paid_middle_313
  · change middlePayment 314 ≤ middleValue ((point 4 cut 1024 314+point 4 cut 1024 315)/2)
    have hp : middlePayment 314 = (637824736832:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 314+point 4 cut 1024 315)/2 = (84536737:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84536737:ℝ)/21094400) = (33971200:ℝ)/21453407 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84536737:ℝ)/21094400)-4 = (159137:ℝ)/21094400 by norm_num]
    exact paid_middle_314
  · change middlePayment 315 ≤ middleValue ((point 4 cut 1024 315+point 4 cut 1024 316)/2)
    have hp : middlePayment 315 = (637864093014:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 315+point 4 cut 1024 316)/2 = (84537243:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84537243:ℝ)/21094400) = (33971200:ℝ)/21452901 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84537243:ℝ)/21094400)-4 = (159643:ℝ)/21094400 by norm_num]
    exact paid_middle_315
  · change middlePayment 316 ≤ middleValue ((point 4 cut 1024 316+point 4 cut 1024 317)/2)
    have hp : middlePayment 316 = (637903450723:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 316+point 4 cut 1024 317)/2 = (84537749:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84537749:ℝ)/21094400) = (6794240:ℝ)/4290479 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84537749:ℝ)/21094400)-4 = (160149:ℝ)/21094400 by norm_num]
    exact paid_middle_316
  · change middlePayment 317 ≤ middleValue ((point 4 cut 1024 317+point 4 cut 1024 318)/2)
    have hp : middlePayment 317 = (637942809958:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 317+point 4 cut 1024 318)/2 = (16907651:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16907651:ℝ)/4218880) = (33971200:ℝ)/21451889 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16907651:ℝ)/4218880)-4 = (32131:ℝ)/4218880 by norm_num]
    exact paid_middle_317
  · change middlePayment 318 ≤ middleValue ((point 4 cut 1024 318+point 4 cut 1024 319)/2)
    have hp : middlePayment 318 = (637982170721:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 318+point 4 cut 1024 319)/2 = (84538761:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84538761:ℝ)/21094400) = (33971200:ℝ)/21451383 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84538761:ℝ)/21094400)-4 = (161161:ℝ)/21094400 by norm_num]
    exact paid_middle_318
  · change middlePayment 319 ≤ middleValue ((point 4 cut 1024 319+point 4 cut 1024 320)/2)
    have hp : middlePayment 319 = (638021533011:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 319+point 4 cut 1024 320)/2 = (84539267:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84539267:ℝ)/21094400) = (33971200:ℝ)/21450877 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84539267:ℝ)/21094400)-4 = (161667:ℝ)/21094400 by norm_num]
    exact paid_middle_319
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_019
