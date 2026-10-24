import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthMiddlePoints050
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem middle_grid_block_050 (j : Fin 16) : middlePayment (16*50+j.val) ≤
    middleValue ((point 4 cut 1024 (16*50+j.val)+point 4 cut 1024 (16*50+j.val+1))/2) := by
  fin_cases j
  · change middlePayment 800 ≤ middleValue ((point 4 cut 1024 800+point 4 cut 1024 801)/2)
    have hp : middlePayment 800 = (657133271844:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 800+point 4 cut 1024 801)/2 = (84782653:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84782653:ℝ)/21094400) = (33971200:ℝ)/21207491 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84782653:ℝ)/21094400)-4 = (405053:ℝ)/21094400 by norm_num]
    exact paid_middle_800
  · change middlePayment 801 ≤ middleValue ((point 4 cut 1024 801+point 4 cut 1024 802)/2)
    have hp : middlePayment 801 = (657173379276:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 801+point 4 cut 1024 802)/2 = (84783159:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84783159:ℝ)/21094400) = (6794240:ℝ)/4241397 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84783159:ℝ)/21094400)-4 = (405559:ℝ)/21094400 by norm_num]
    exact paid_middle_801
  · change middlePayment 802 ≤ middleValue ((point 4 cut 1024 802+point 4 cut 1024 803)/2)
    have hp : middlePayment 802 = (657213488274:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 802+point 4 cut 1024 803)/2 = (16956733:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16956733:ℝ)/4218880) = (33971200:ℝ)/21206479 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16956733:ℝ)/4218880)-4 = (81213:ℝ)/4218880 by norm_num]
    exact paid_middle_802
  · change middlePayment 803 ≤ middleValue ((point 4 cut 1024 803+point 4 cut 1024 804)/2)
    have hp : middlePayment 803 = (657253598836:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 803+point 4 cut 1024 804)/2 = (84784171:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84784171:ℝ)/21094400) = (33971200:ℝ)/21205973 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84784171:ℝ)/21094400)-4 = (406571:ℝ)/21094400 by norm_num]
    exact paid_middle_803
  · change middlePayment 804 ≤ middleValue ((point 4 cut 1024 804+point 4 cut 1024 805)/2)
    have hp : middlePayment 804 = (657293710964:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 804+point 4 cut 1024 805)/2 = (84784677:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84784677:ℝ)/21094400) = (33971200:ℝ)/21205467 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84784677:ℝ)/21094400)-4 = (407077:ℝ)/21094400 by norm_num]
    exact paid_middle_804
  · change middlePayment 805 ≤ middleValue ((point 4 cut 1024 805+point 4 cut 1024 806)/2)
    have hp : middlePayment 805 = (657333824657:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 805+point 4 cut 1024 806)/2 = (84785183:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84785183:ℝ)/21094400) = (33971200:ℝ)/21204961 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84785183:ℝ)/21094400)-4 = (407583:ℝ)/21094400 by norm_num]
    exact paid_middle_805
  · change middlePayment 806 ≤ middleValue ((point 4 cut 1024 806+point 4 cut 1024 807)/2)
    have hp : middlePayment 806 = (657373939915:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 806+point 4 cut 1024 807)/2 = (84785689:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84785689:ℝ)/21094400) = (6794240:ℝ)/4240891 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84785689:ℝ)/21094400)-4 = (408089:ℝ)/21094400 by norm_num]
    exact paid_middle_806
  · change middlePayment 807 ≤ middleValue ((point 4 cut 1024 807+point 4 cut 1024 808)/2)
    have hp : middlePayment 807 = (657414056739:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 807+point 4 cut 1024 808)/2 = (16957239:ℝ)/4218880 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((16957239:ℝ)/4218880) = (33971200:ℝ)/21203949 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((16957239:ℝ)/4218880)-4 = (81719:ℝ)/4218880 by norm_num]
    exact paid_middle_807
  · change middlePayment 808 ≤ middleValue ((point 4 cut 1024 808+point 4 cut 1024 809)/2)
    have hp : middlePayment 808 = (657454175127:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 808+point 4 cut 1024 809)/2 = (84786701:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84786701:ℝ)/21094400) = (33971200:ℝ)/21203443 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84786701:ℝ)/21094400)-4 = (409101:ℝ)/21094400 by norm_num]
    exact paid_middle_808
  · change middlePayment 809 ≤ middleValue ((point 4 cut 1024 809+point 4 cut 1024 810)/2)
    have hp : middlePayment 809 = (657494295082:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 809+point 4 cut 1024 810)/2 = (84787207:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84787207:ℝ)/21094400) = (33971200:ℝ)/21202937 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84787207:ℝ)/21094400)-4 = (409607:ℝ)/21094400 by norm_num]
    exact paid_middle_809
  · change middlePayment 810 ≤ middleValue ((point 4 cut 1024 810+point 4 cut 1024 811)/2)
    have hp : middlePayment 810 = (657534416602:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 810+point 4 cut 1024 811)/2 = (84787713:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84787713:ℝ)/21094400) = (33971200:ℝ)/21202431 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84787713:ℝ)/21094400)-4 = (410113:ℝ)/21094400 by norm_num]
    exact paid_middle_810
  · change middlePayment 811 ≤ middleValue ((point 4 cut 1024 811+point 4 cut 1024 812)/2)
    have hp : middlePayment 811 = (657574539687:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 811+point 4 cut 1024 812)/2 = (84788219:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84788219:ℝ)/21094400) = (1358848:ℝ)/848077 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84788219:ℝ)/21094400)-4 = (410619:ℝ)/21094400 by norm_num]
    exact paid_middle_811
  · change middlePayment 812 ≤ middleValue ((point 4 cut 1024 812+point 4 cut 1024 813)/2)
    have hp : middlePayment 812 = (657614664339:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 812+point 4 cut 1024 813)/2 = (3391549:ℝ)/843776 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((3391549:ℝ)/843776) = (33971200:ℝ)/21201419 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((3391549:ℝ)/843776)-4 = (16445:ℝ)/843776 by norm_num]
    exact paid_middle_812
  · change middlePayment 813 ≤ middleValue ((point 4 cut 1024 813+point 4 cut 1024 814)/2)
    have hp : middlePayment 813 = (657654790556:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 813+point 4 cut 1024 814)/2 = (84789231:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84789231:ℝ)/21094400) = (33971200:ℝ)/21200913 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84789231:ℝ)/21094400)-4 = (411631:ℝ)/21094400 by norm_num]
    exact paid_middle_813
  · change middlePayment 814 ≤ middleValue ((point 4 cut 1024 814+point 4 cut 1024 815)/2)
    have hp : middlePayment 814 = (657694918339:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 814+point 4 cut 1024 815)/2 = (84789737:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84789737:ℝ)/21094400) = (33971200:ℝ)/21200407 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84789737:ℝ)/21094400)-4 = (412137:ℝ)/21094400 by norm_num]
    exact paid_middle_814
  · change middlePayment 815 ≤ middleValue ((point 4 cut 1024 815+point 4 cut 1024 816)/2)
    have hp : middlePayment 815 = (657735047688:ℝ)/1000000000000 := rfl
    have hx : (point 4 cut 1024 815+point 4 cut 1024 816)/2 = (84790243:ℝ)/21094400 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((84790243:ℝ)/21094400) = (33971200:ℝ)/21199901 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold middleValue
    rw [hr]
    rw [show ((84790243:ℝ)/21094400)-4 = (412643:ℝ)/21094400 by norm_num]
    exact paid_middle_815
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.middle_grid_block_050
