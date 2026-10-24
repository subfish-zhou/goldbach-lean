import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints062
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_062 (j : Fin 16) : terminalPayment (16*62+j.val) ≤
    terminalValue ((point cut hi 1024 (16*62+j.val)+point cut hi 1024 (16*62+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 992 ≤ terminalValue ((point cut hi 1024 992+point cut hi 1024 993)/2)
    have hp : terminalPayment 992 = (34166313099:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 992+point cut hi 1024 993)/2 = (194752863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194752863:ℝ)/42188800) = (1719241:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194752863:ℝ)/42188800)-4 = (25997663:ℝ)/42188800 by norm_num]
    exact paid_terminal_992
  · change terminalPayment 993 ≤ terminalValue ((point cut hi 1024 993+point cut hi 1024 994)/2)
    have hp : terminalPayment 993 = (33101390359:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 993+point cut hi 1024 994)/2 = (194778013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194778013:ℝ)/42188800) = (1718235:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194778013:ℝ)/42188800)-4 = (26022813:ℝ)/42188800 by norm_num]
    exact paid_terminal_993
  · change terminalPayment 994 ≤ terminalValue ((point cut hi 1024 994+point cut hi 1024 995)/2)
    have hp : terminalPayment 994 = (32035192774:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 994+point cut hi 1024 995)/2 = (194803163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194803163:ℝ)/42188800) = (1717229:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194803163:ℝ)/42188800)-4 = (26047963:ℝ)/42188800 by norm_num]
    exact paid_terminal_994
  · change terminalPayment 995 ≤ terminalValue ((point cut hi 1024 995+point cut hi 1024 996)/2)
    have hp : terminalPayment 995 = (30967718499:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 995+point cut hi 1024 996)/2 = (194828313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194828313:ℝ)/42188800) = (1716223:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194828313:ℝ)/42188800)-4 = (26073113:ℝ)/42188800 by norm_num]
    exact paid_terminal_995
  · change terminalPayment 996 ≤ terminalValue ((point cut hi 1024 996+point cut hi 1024 997)/2)
    have hp : terminalPayment 996 = (29898965684:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 996+point cut hi 1024 997)/2 = (194853463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194853463:ℝ)/42188800) = (1715217:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194853463:ℝ)/42188800)-4 = (26098263:ℝ)/42188800 by norm_num]
    exact paid_terminal_996
  · change terminalPayment 997 ≤ terminalValue ((point cut hi 1024 997+point cut hi 1024 998)/2)
    have hp : terminalPayment 997 = (28828932473:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 997+point cut hi 1024 998)/2 = (194878613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194878613:ℝ)/42188800) = (1714211:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194878613:ℝ)/42188800)-4 = (26123413:ℝ)/42188800 by norm_num]
    exact paid_terminal_997
  · change terminalPayment 998 ≤ terminalValue ((point cut hi 1024 998+point cut hi 1024 999)/2)
    have hp : terminalPayment 998 = (27757617011:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 998+point cut hi 1024 999)/2 = (194903763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194903763:ℝ)/42188800) = (1713205:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194903763:ℝ)/42188800)-4 = (26148563:ℝ)/42188800 by norm_num]
    exact paid_terminal_998
  · change terminalPayment 999 ≤ terminalValue ((point cut hi 1024 999+point cut hi 1024 1000)/2)
    have hp : terminalPayment 999 = (26685017435:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 999+point cut hi 1024 1000)/2 = (194928913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194928913:ℝ)/42188800) = (1712199:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194928913:ℝ)/42188800)-4 = (26173713:ℝ)/42188800 by norm_num]
    exact paid_terminal_999
  · change terminalPayment 1000 ≤ terminalValue ((point cut hi 1024 1000+point cut hi 1024 1001)/2)
    have hp : terminalPayment 1000 = (25611131882:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1000+point cut hi 1024 1001)/2 = (194954063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194954063:ℝ)/42188800) = (1711193:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194954063:ℝ)/42188800)-4 = (26198863:ℝ)/42188800 by norm_num]
    exact paid_terminal_1000
  · change terminalPayment 1001 ≤ terminalValue ((point cut hi 1024 1001+point cut hi 1024 1002)/2)
    have hp : terminalPayment 1001 = (24535958484:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1001+point cut hi 1024 1002)/2 = (194979213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194979213:ℝ)/42188800) = (1710187:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194979213:ℝ)/42188800)-4 = (26224013:ℝ)/42188800 by norm_num]
    exact paid_terminal_1001
  · change terminalPayment 1002 ≤ terminalValue ((point cut hi 1024 1002+point cut hi 1024 1003)/2)
    have hp : terminalPayment 1002 = (23459495368:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1002+point cut hi 1024 1003)/2 = (195004363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195004363:ℝ)/42188800) = (1709181:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195004363:ℝ)/42188800)-4 = (26249163:ℝ)/42188800 by norm_num]
    exact paid_terminal_1002
  · change terminalPayment 1003 ≤ terminalValue ((point cut hi 1024 1003+point cut hi 1024 1004)/2)
    have hp : terminalPayment 1003 = (22381740660:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1003+point cut hi 1024 1004)/2 = (195029513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195029513:ℝ)/42188800) = (1708175:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195029513:ℝ)/42188800)-4 = (26274313:ℝ)/42188800 by norm_num]
    exact paid_terminal_1003
  · change terminalPayment 1004 ≤ terminalValue ((point cut hi 1024 1004+point cut hi 1024 1005)/2)
    have hp : terminalPayment 1004 = (21302692480:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1004+point cut hi 1024 1005)/2 = (195054663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195054663:ℝ)/42188800) = (1707169:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195054663:ℝ)/42188800)-4 = (26299463:ℝ)/42188800 by norm_num]
    exact paid_terminal_1004
  · change terminalPayment 1005 ≤ terminalValue ((point cut hi 1024 1005+point cut hi 1024 1006)/2)
    have hp : terminalPayment 1005 = (20222348947:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1005+point cut hi 1024 1006)/2 = (195079813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195079813:ℝ)/42188800) = (1706163:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195079813:ℝ)/42188800)-4 = (26324613:ℝ)/42188800 by norm_num]
    exact paid_terminal_1005
  · change terminalPayment 1006 ≤ terminalValue ((point cut hi 1024 1006+point cut hi 1024 1007)/2)
    have hp : terminalPayment 1006 = (19140708174:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1006+point cut hi 1024 1007)/2 = (195104963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195104963:ℝ)/42188800) = (1705157:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195104963:ℝ)/42188800)-4 = (26349763:ℝ)/42188800 by norm_num]
    exact paid_terminal_1006
  · change terminalPayment 1007 ≤ terminalValue ((point cut hi 1024 1007+point cut hi 1024 1008)/2)
    have hp : terminalPayment 1007 = (18057768273:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1007+point cut hi 1024 1008)/2 = (195130113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195130113:ℝ)/42188800) = (1704151:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195130113:ℝ)/42188800)-4 = (26374913:ℝ)/42188800 by norm_num]
    exact paid_terminal_1007
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_062
