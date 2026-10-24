import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints063
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_063 (j : Fin 16) : terminalPayment (16*63+j.val) ≤
    terminalValue ((point cut hi 1024 (16*63+j.val)+point cut hi 1024 (16*63+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 1008 ≤ terminalValue ((point cut hi 1024 1008+point cut hi 1024 1009)/2)
    have hp : terminalPayment 1008 = (16973527349:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1008+point cut hi 1024 1009)/2 = (195155263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195155263:ℝ)/42188800) = (1703145:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195155263:ℝ)/42188800)-4 = (26400063:ℝ)/42188800 by norm_num]
    exact paid_terminal_1008
  · change terminalPayment 1009 ≤ terminalValue ((point cut hi 1024 1009+point cut hi 1024 1010)/2)
    have hp : terminalPayment 1009 = (15887983505:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1009+point cut hi 1024 1010)/2 = (195180413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195180413:ℝ)/42188800) = (1702139:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195180413:ℝ)/42188800)-4 = (26425213:ℝ)/42188800 by norm_num]
    exact paid_terminal_1009
  · change terminalPayment 1010 ≤ terminalValue ((point cut hi 1024 1010+point cut hi 1024 1011)/2)
    have hp : terminalPayment 1010 = (14801134843:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1010+point cut hi 1024 1011)/2 = (195205563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195205563:ℝ)/42188800) = (1701133:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195205563:ℝ)/42188800)-4 = (26450363:ℝ)/42188800 by norm_num]
    exact paid_terminal_1010
  · change terminalPayment 1011 ≤ terminalValue ((point cut hi 1024 1011+point cut hi 1024 1012)/2)
    have hp : terminalPayment 1011 = (13712979456:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1011+point cut hi 1024 1012)/2 = (195230713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195230713:ℝ)/42188800) = (1700127:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195230713:ℝ)/42188800)-4 = (26475513:ℝ)/42188800 by norm_num]
    exact paid_terminal_1011
  · change terminalPayment 1012 ≤ terminalValue ((point cut hi 1024 1012+point cut hi 1024 1013)/2)
    have hp : terminalPayment 1012 = (12623515438:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1012+point cut hi 1024 1013)/2 = (195255863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195255863:ℝ)/42188800) = (1699121:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195255863:ℝ)/42188800)-4 = (26500663:ℝ)/42188800 by norm_num]
    exact paid_terminal_1012
  · change terminalPayment 1013 ≤ terminalValue ((point cut hi 1024 1013+point cut hi 1024 1014)/2)
    have hp : terminalPayment 1013 = (11532740878:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1013+point cut hi 1024 1014)/2 = (195281013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195281013:ℝ)/42188800) = (1698115:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195281013:ℝ)/42188800)-4 = (26525813:ℝ)/42188800 by norm_num]
    exact paid_terminal_1013
  · change terminalPayment 1014 ≤ terminalValue ((point cut hi 1024 1014+point cut hi 1024 1015)/2)
    have hp : terminalPayment 1014 = (10440653859:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1014+point cut hi 1024 1015)/2 = (195306163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195306163:ℝ)/42188800) = (1697109:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195306163:ℝ)/42188800)-4 = (26550963:ℝ)/42188800 by norm_num]
    exact paid_terminal_1014
  · change terminalPayment 1015 ≤ terminalValue ((point cut hi 1024 1015+point cut hi 1024 1016)/2)
    have hp : terminalPayment 1015 = (9347252464:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1015+point cut hi 1024 1016)/2 = (195331313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195331313:ℝ)/42188800) = (1696103:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195331313:ℝ)/42188800)-4 = (26576113:ℝ)/42188800 by norm_num]
    exact paid_terminal_1015
  · change terminalPayment 1016 ≤ terminalValue ((point cut hi 1024 1016+point cut hi 1024 1017)/2)
    have hp : terminalPayment 1016 = (8252534769:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1016+point cut hi 1024 1017)/2 = (195356463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195356463:ℝ)/42188800) = (1695097:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195356463:ℝ)/42188800)-4 = (26601263:ℝ)/42188800 by norm_num]
    exact paid_terminal_1016
  · change terminalPayment 1017 ≤ terminalValue ((point cut hi 1024 1017+point cut hi 1024 1018)/2)
    have hp : terminalPayment 1017 = (7156498850:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1017+point cut hi 1024 1018)/2 = (195381613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195381613:ℝ)/42188800) = (1694091:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195381613:ℝ)/42188800)-4 = (26626413:ℝ)/42188800 by norm_num]
    exact paid_terminal_1017
  · change terminalPayment 1018 ≤ terminalValue ((point cut hi 1024 1018+point cut hi 1024 1019)/2)
    have hp : terminalPayment 1018 = (6059142775:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1018+point cut hi 1024 1019)/2 = (195406763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195406763:ℝ)/42188800) = (1693085:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195406763:ℝ)/42188800)-4 = (26651563:ℝ)/42188800 by norm_num]
    exact paid_terminal_1018
  · change terminalPayment 1019 ≤ terminalValue ((point cut hi 1024 1019+point cut hi 1024 1020)/2)
    have hp : terminalPayment 1019 = (4960464611:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1019+point cut hi 1024 1020)/2 = (195431913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195431913:ℝ)/42188800) = (1692079:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195431913:ℝ)/42188800)-4 = (26676713:ℝ)/42188800 by norm_num]
    exact paid_terminal_1019
  · change terminalPayment 1020 ≤ terminalValue ((point cut hi 1024 1020+point cut hi 1024 1021)/2)
    have hp : terminalPayment 1020 = (3860462422:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1020+point cut hi 1024 1021)/2 = (195457063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195457063:ℝ)/42188800) = (1691073:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195457063:ℝ)/42188800)-4 = (26701863:ℝ)/42188800 by norm_num]
    exact paid_terminal_1020
  · change terminalPayment 1021 ≤ terminalValue ((point cut hi 1024 1021+point cut hi 1024 1022)/2)
    have hp : terminalPayment 1021 = (2759134266:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1021+point cut hi 1024 1022)/2 = (195482213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195482213:ℝ)/42188800) = (1690067:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195482213:ℝ)/42188800)-4 = (26727013:ℝ)/42188800 by norm_num]
    exact paid_terminal_1021
  · change terminalPayment 1022 ≤ terminalValue ((point cut hi 1024 1022+point cut hi 1024 1023)/2)
    have hp : terminalPayment 1022 = (1656478199:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1022+point cut hi 1024 1023)/2 = (195507363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195507363:ℝ)/42188800) = (1689061:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195507363:ℝ)/42188800)-4 = (26752163:ℝ)/42188800 by norm_num]
    exact paid_terminal_1022
  · change terminalPayment 1023 ≤ terminalValue ((point cut hi 1024 1023+point cut hi 1024 1024)/2)
    have hp : terminalPayment 1023 = (552492271:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1023+point cut hi 1024 1024)/2 = (195532513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((195532513:ℝ)/42188800) = (1688055:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((195532513:ℝ)/42188800)-4 = (26777313:ℝ)/42188800 by norm_num]
    exact paid_terminal_1023
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_063
