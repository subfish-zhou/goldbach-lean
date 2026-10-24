import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints061
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_061 (j : Fin 16) : terminalPayment (16*61+j.val) ≤
    terminalValue ((point cut hi 1024 (16*61+j.val)+point cut hi 1024 (16*61+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 976 ≤ terminalValue ((point cut hi 1024 976+point cut hi 1024 977)/2)
    have hp : terminalPayment 976 = (51033191720:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 976+point cut hi 1024 977)/2 = (194350463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194350463:ℝ)/42188800) = (1735337:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194350463:ℝ)/42188800)-4 = (25595263:ℝ)/42188800 by norm_num]
    exact paid_terminal_976
  · change terminalPayment 977 ≤ terminalValue ((point cut hi 1024 977+point cut hi 1024 978)/2)
    have hp : terminalPayment 977 = (49988418148:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 977+point cut hi 1024 978)/2 = (194375613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194375613:ℝ)/42188800) = (1734331:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194375613:ℝ)/42188800)-4 = (25620413:ℝ)/42188800 by norm_num]
    exact paid_terminal_977
  · change terminalPayment 978 ≤ terminalValue ((point cut hi 1024 978+point cut hi 1024 979)/2)
    have hp : terminalPayment 978 = (48942398809:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 978+point cut hi 1024 979)/2 = (194400763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194400763:ℝ)/42188800) = (1733325:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194400763:ℝ)/42188800)-4 = (25645563:ℝ)/42188800 by norm_num]
    exact paid_terminal_978
  · change terminalPayment 979 ≤ terminalValue ((point cut hi 1024 979+point cut hi 1024 980)/2)
    have hp : terminalPayment 979 = (47895131913:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 979+point cut hi 1024 980)/2 = (194425913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194425913:ℝ)/42188800) = (1732319:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194425913:ℝ)/42188800)-4 = (25670713:ℝ)/42188800 by norm_num]
    exact paid_terminal_979
  · change terminalPayment 980 ≤ terminalValue ((point cut hi 1024 980+point cut hi 1024 981)/2)
    have hp : terminalPayment 980 = (46846615664:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 980+point cut hi 1024 981)/2 = (194451063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194451063:ℝ)/42188800) = (1731313:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194451063:ℝ)/42188800)-4 = (25695863:ℝ)/42188800 by norm_num]
    exact paid_terminal_980
  · change terminalPayment 981 ≤ terminalValue ((point cut hi 1024 981+point cut hi 1024 982)/2)
    have hp : terminalPayment 981 = (45796848263:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 981+point cut hi 1024 982)/2 = (194476213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194476213:ℝ)/42188800) = (1730307:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194476213:ℝ)/42188800)-4 = (25721013:ℝ)/42188800 by norm_num]
    exact paid_terminal_981
  · change terminalPayment 982 ≤ terminalValue ((point cut hi 1024 982+point cut hi 1024 983)/2)
    have hp : terminalPayment 982 = (44745827910:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 982+point cut hi 1024 983)/2 = (194501363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194501363:ℝ)/42188800) = (1729301:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194501363:ℝ)/42188800)-4 = (25746163:ℝ)/42188800 by norm_num]
    exact paid_terminal_982
  · change terminalPayment 983 ≤ terminalValue ((point cut hi 1024 983+point cut hi 1024 984)/2)
    have hp : terminalPayment 983 = (43693552798:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 983+point cut hi 1024 984)/2 = (194526513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194526513:ℝ)/42188800) = (1728295:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194526513:ℝ)/42188800)-4 = (25771313:ℝ)/42188800 by norm_num]
    exact paid_terminal_983
  · change terminalPayment 984 ≤ terminalValue ((point cut hi 1024 984+point cut hi 1024 985)/2)
    have hp : terminalPayment 984 = (42640021119:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 984+point cut hi 1024 985)/2 = (194551663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194551663:ℝ)/42188800) = (1727289:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194551663:ℝ)/42188800)-4 = (25796463:ℝ)/42188800 by norm_num]
    exact paid_terminal_984
  · change terminalPayment 985 ≤ terminalValue ((point cut hi 1024 985+point cut hi 1024 986)/2)
    have hp : terminalPayment 985 = (41585231061:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 985+point cut hi 1024 986)/2 = (194576813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194576813:ℝ)/42188800) = (1726283:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194576813:ℝ)/42188800)-4 = (25821613:ℝ)/42188800 by norm_num]
    exact paid_terminal_985
  · change terminalPayment 986 ≤ terminalValue ((point cut hi 1024 986+point cut hi 1024 987)/2)
    have hp : terminalPayment 986 = (40529180808:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 986+point cut hi 1024 987)/2 = (194601963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194601963:ℝ)/42188800) = (1725277:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194601963:ℝ)/42188800)-4 = (25846763:ℝ)/42188800 by norm_num]
    exact paid_terminal_986
  · change terminalPayment 987 ≤ terminalValue ((point cut hi 1024 987+point cut hi 1024 988)/2)
    have hp : terminalPayment 987 = (39471868542:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 987+point cut hi 1024 988)/2 = (194627113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194627113:ℝ)/42188800) = (1724271:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194627113:ℝ)/42188800)-4 = (25871913:ℝ)/42188800 by norm_num]
    exact paid_terminal_987
  · change terminalPayment 988 ≤ terminalValue ((point cut hi 1024 988+point cut hi 1024 989)/2)
    have hp : terminalPayment 988 = (38413292440:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 988+point cut hi 1024 989)/2 = (194652263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194652263:ℝ)/42188800) = (1723265:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194652263:ℝ)/42188800)-4 = (25897063:ℝ)/42188800 by norm_num]
    exact paid_terminal_988
  · change terminalPayment 989 ≤ terminalValue ((point cut hi 1024 989+point cut hi 1024 990)/2)
    have hp : terminalPayment 989 = (37353450675:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 989+point cut hi 1024 990)/2 = (194677413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194677413:ℝ)/42188800) = (1722259:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194677413:ℝ)/42188800)-4 = (25922213:ℝ)/42188800 by norm_num]
    exact paid_terminal_989
  · change terminalPayment 990 ≤ terminalValue ((point cut hi 1024 990+point cut hi 1024 991)/2)
    have hp : terminalPayment 990 = (36292341420:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 990+point cut hi 1024 991)/2 = (194702563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194702563:ℝ)/42188800) = (1721253:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194702563:ℝ)/42188800)-4 = (25947363:ℝ)/42188800 by norm_num]
    exact paid_terminal_990
  · change terminalPayment 991 ≤ terminalValue ((point cut hi 1024 991+point cut hi 1024 992)/2)
    have hp : terminalPayment 991 = (35229962840:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 991+point cut hi 1024 992)/2 = (194727713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194727713:ℝ)/42188800) = (1720247:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194727713:ℝ)/42188800)-4 = (25972513:ℝ)/42188800 by norm_num]
    exact paid_terminal_991
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_061
