import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints003
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_003 (j : Fin 16) : middlePayment (16*3+j.val) ≤
    middleValue ((point 4 cut 1024 (16*3+j.val)+point 4 cut 1024 (16*3+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 48 ≤ middleValue ((point 4 cut 1024 48+point 4 cut 1024 49)/2)
    have hp : middlePayment 48 = (627409973278:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 48+point 4 cut 1024 49)/2 = (84402141:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84402141:ℝ)/21094400) = (33971200:ℝ)/21588003 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84402141:ℝ)/21094400)-4 = (24541:ℝ)/21094400 by norm_num]
    exact paid_middle_48
  · change middlePayment 49 ≤ middleValue ((point 4 cut 1024 49+point 4 cut 1024 50)/2)
    have hp : middlePayment 49 = (627448926002:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 49+point 4 cut 1024 50)/2 = (84402647:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84402647:ℝ)/21094400) = (33971200:ℝ)/21587497 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84402647:ℝ)/21094400)-4 = (25047:ℝ)/21094400 by norm_num]
    exact paid_middle_49
  · change middlePayment 50 ≤ middleValue ((point 4 cut 1024 50+point 4 cut 1024 51)/2)
    have hp : middlePayment 50 = (627487880234:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 50+point 4 cut 1024 51)/2 = (84403153:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84403153:ℝ)/21094400) = (33971200:ℝ)/21586991 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84403153:ℝ)/21094400)-4 = (25553:ℝ)/21094400 by norm_num]
    exact paid_middle_50
  · change middlePayment 51 ≤ middleValue ((point 4 cut 1024 51+point 4 cut 1024 52)/2)
    have hp : middlePayment 51 = (627526835972:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 51+point 4 cut 1024 52)/2 = (819453:ℝ)/204800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((819453:ℝ)/204800) = (6794240:ℝ)/4317297 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((819453:ℝ)/204800)-4 = (253:ℝ)/204800 by norm_num]
    exact paid_middle_51
  · change middlePayment 52 ≤ middleValue ((point 4 cut 1024 52+point 4 cut 1024 53)/2)
    have hp : middlePayment 52 = (627565793217:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 52+point 4 cut 1024 53)/2 = (16880833:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16880833:ℝ)/4218880) = (33971200:ℝ)/21585979 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16880833:ℝ)/4218880)-4 = (5313:ℝ)/4218880 by norm_num]
    exact paid_middle_52
  · change middlePayment 53 ≤ middleValue ((point 4 cut 1024 53+point 4 cut 1024 54)/2)
    have hp : middlePayment 53 = (627604751968:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 53+point 4 cut 1024 54)/2 = (84404671:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84404671:ℝ)/21094400) = (33971200:ℝ)/21585473 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84404671:ℝ)/21094400)-4 = (27071:ℝ)/21094400 by norm_num]
    exact paid_middle_53
  · change middlePayment 54 ≤ middleValue ((point 4 cut 1024 54+point 4 cut 1024 55)/2)
    have hp : middlePayment 54 = (627643712227:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 54+point 4 cut 1024 55)/2 = (84405177:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84405177:ℝ)/21094400) = (33971200:ℝ)/21584967 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84405177:ℝ)/21094400)-4 = (27577:ℝ)/21094400 by norm_num]
    exact paid_middle_54
  · change middlePayment 55 ≤ middleValue ((point 4 cut 1024 55+point 4 cut 1024 56)/2)
    have hp : middlePayment 55 = (627682673993:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 55+point 4 cut 1024 56)/2 = (84405683:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84405683:ℝ)/21094400) = (33971200:ℝ)/21584461 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84405683:ℝ)/21094400)-4 = (28083:ℝ)/21094400 by norm_num]
    exact paid_middle_55
  · change middlePayment 56 ≤ middleValue ((point 4 cut 1024 56+point 4 cut 1024 57)/2)
    have hp : middlePayment 56 = (627721637266:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 56+point 4 cut 1024 57)/2 = (84406189:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84406189:ℝ)/21094400) = (6794240:ℝ)/4316791 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84406189:ℝ)/21094400)-4 = (28589:ℝ)/21094400 by norm_num]
    exact paid_middle_56
  · change middlePayment 57 ≤ middleValue ((point 4 cut 1024 57+point 4 cut 1024 58)/2)
    have hp : middlePayment 57 = (627760602047:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 57+point 4 cut 1024 58)/2 = (16881339:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16881339:ℝ)/4218880) = (33971200:ℝ)/21583449 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16881339:ℝ)/4218880)-4 = (5819:ℝ)/4218880 by norm_num]
    exact paid_middle_57
  · change middlePayment 58 ≤ middleValue ((point 4 cut 1024 58+point 4 cut 1024 59)/2)
    have hp : middlePayment 58 = (627799568334:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 58+point 4 cut 1024 59)/2 = (84407201:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84407201:ℝ)/21094400) = (33971200:ℝ)/21582943 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84407201:ℝ)/21094400)-4 = (29601:ℝ)/21094400 by norm_num]
    exact paid_middle_58
  · change middlePayment 59 ≤ middleValue ((point 4 cut 1024 59+point 4 cut 1024 60)/2)
    have hp : middlePayment 59 = (627838536129:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 59+point 4 cut 1024 60)/2 = (84407707:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84407707:ℝ)/21094400) = (33971200:ℝ)/21582437 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84407707:ℝ)/21094400)-4 = (30107:ℝ)/21094400 by norm_num]
    exact paid_middle_59
  · change middlePayment 60 ≤ middleValue ((point 4 cut 1024 60+point 4 cut 1024 61)/2)
    have hp : middlePayment 60 = (627877505432:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 60+point 4 cut 1024 61)/2 = (84408213:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84408213:ℝ)/21094400) = (33971200:ℝ)/21581931 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84408213:ℝ)/21094400)-4 = (30613:ℝ)/21094400 by norm_num]
    exact paid_middle_60
  · change middlePayment 61 ≤ middleValue ((point 4 cut 1024 61+point 4 cut 1024 62)/2)
    have hp : middlePayment 61 = (627916476242:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 61+point 4 cut 1024 62)/2 = (84408719:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84408719:ℝ)/21094400) = (1358848:ℝ)/863257 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84408719:ℝ)/21094400)-4 = (31119:ℝ)/21094400 by norm_num]
    exact paid_middle_61
  · change middlePayment 62 ≤ middleValue ((point 4 cut 1024 62+point 4 cut 1024 63)/2)
    have hp : middlePayment 62 = (627955448559:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 62+point 4 cut 1024 63)/2 = (3376369:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3376369:ℝ)/843776) = (33971200:ℝ)/21580919 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3376369:ℝ)/843776)-4 = (1265:ℝ)/843776 by norm_num]
    exact paid_middle_62
  · change middlePayment 63 ≤ middleValue ((point 4 cut 1024 63+point 4 cut 1024 64)/2)
    have hp : middlePayment 63 = (627994422385:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 63+point 4 cut 1024 64)/2 = (84409731:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84409731:ℝ)/21094400) = (33971200:ℝ)/21580413 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84409731:ℝ)/21094400)-4 = (32131:ℝ)/21094400 by norm_num]
    exact paid_middle_63
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_003
