import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints000
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_000 (j : Fin 16) : terminalPayment (16*0+j.val) ≤
    terminalValue ((point cut hi 1024 (16*0+j.val)+point cut hi 1024 (16*0+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 0 ≤ terminalValue ((point cut hi 1024 0+point cut hi 1024 1)/2)
    have hp : terminalPayment 0 = (665963598650:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 0+point cut hi 1024 1)/2 = (169804063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((169804063:ℝ)/42188800) = (2717193:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((169804063:ℝ)/42188800)-4 = (1048863:ℝ)/42188800 by norm_num]
    exact paid_terminal_0
  · change terminalPayment 1 ≤ terminalValue ((point cut hi 1024 1+point cut hi 1024 2)/2)
    have hp : terminalPayment 1 = (665617807730:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 1+point cut hi 1024 2)/2 = (169829213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((169829213:ℝ)/42188800) = (2716187:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((169829213:ℝ)/42188800)-4 = (1074013:ℝ)/42188800 by norm_num]
    exact paid_terminal_1
  · change terminalPayment 2 ≤ terminalValue ((point cut hi 1024 2+point cut hi 1024 3)/2)
    have hp : terminalPayment 2 = (665271607524:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 2+point cut hi 1024 3)/2 = (169854363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((169854363:ℝ)/42188800) = (2715181:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((169854363:ℝ)/42188800)-4 = (1099163:ℝ)/42188800 by norm_num]
    exact paid_terminal_2
  · change terminalPayment 3 ≤ terminalValue ((point cut hi 1024 3+point cut hi 1024 4)/2)
    have hp : terminalPayment 3 = (664924997700:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 3+point cut hi 1024 4)/2 = (169879513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((169879513:ℝ)/42188800) = (2714175:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((169879513:ℝ)/42188800)-4 = (1124313:ℝ)/42188800 by norm_num]
    exact paid_terminal_3
  · change terminalPayment 4 ≤ terminalValue ((point cut hi 1024 4+point cut hi 1024 5)/2)
    have hp : terminalPayment 4 = (664577977926:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 4+point cut hi 1024 5)/2 = (169904663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((169904663:ℝ)/42188800) = (2713169:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((169904663:ℝ)/42188800)-4 = (1149463:ℝ)/42188800 by norm_num]
    exact paid_terminal_4
  · change terminalPayment 5 ≤ terminalValue ((point cut hi 1024 5+point cut hi 1024 6)/2)
    have hp : terminalPayment 5 = (664230547867:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 5+point cut hi 1024 6)/2 = (169929813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((169929813:ℝ)/42188800) = (2712163:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((169929813:ℝ)/42188800)-4 = (1174613:ℝ)/42188800 by norm_num]
    exact paid_terminal_5
  · change terminalPayment 6 ≤ terminalValue ((point cut hi 1024 6+point cut hi 1024 7)/2)
    have hp : terminalPayment 6 = (663882707189:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 6+point cut hi 1024 7)/2 = (169954963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((169954963:ℝ)/42188800) = (2711157:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((169954963:ℝ)/42188800)-4 = (1199763:ℝ)/42188800 by norm_num]
    exact paid_terminal_6
  · change terminalPayment 7 ≤ terminalValue ((point cut hi 1024 7+point cut hi 1024 8)/2)
    have hp : terminalPayment 7 = (663534455558:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 7+point cut hi 1024 8)/2 = (169980113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((169980113:ℝ)/42188800) = (2710151:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((169980113:ℝ)/42188800)-4 = (1224913:ℝ)/42188800 by norm_num]
    exact paid_terminal_7
  · change terminalPayment 8 ≤ terminalValue ((point cut hi 1024 8+point cut hi 1024 9)/2)
    have hp : terminalPayment 8 = (663185792637:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 8+point cut hi 1024 9)/2 = (170005263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170005263:ℝ)/42188800) = (2709145:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170005263:ℝ)/42188800)-4 = (1250063:ℝ)/42188800 by norm_num]
    exact paid_terminal_8
  · change terminalPayment 9 ≤ terminalValue ((point cut hi 1024 9+point cut hi 1024 10)/2)
    have hp : terminalPayment 9 = (662836718091:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 9+point cut hi 1024 10)/2 = (170030413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170030413:ℝ)/42188800) = (2708139:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170030413:ℝ)/42188800)-4 = (1275213:ℝ)/42188800 by norm_num]
    exact paid_terminal_9
  · change terminalPayment 10 ≤ terminalValue ((point cut hi 1024 10+point cut hi 1024 11)/2)
    have hp : terminalPayment 10 = (662487231582:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 10+point cut hi 1024 11)/2 = (170055563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170055563:ℝ)/42188800) = (2707133:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170055563:ℝ)/42188800)-4 = (1300363:ℝ)/42188800 by norm_num]
    exact paid_terminal_10
  · change terminalPayment 11 ≤ terminalValue ((point cut hi 1024 11+point cut hi 1024 12)/2)
    have hp : terminalPayment 11 = (662137332774:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 11+point cut hi 1024 12)/2 = (170080713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170080713:ℝ)/42188800) = (2706127:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170080713:ℝ)/42188800)-4 = (1325513:ℝ)/42188800 by norm_num]
    exact paid_terminal_11
  · change terminalPayment 12 ≤ terminalValue ((point cut hi 1024 12+point cut hi 1024 13)/2)
    have hp : terminalPayment 12 = (661787021328:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 12+point cut hi 1024 13)/2 = (170105863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170105863:ℝ)/42188800) = (2705121:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170105863:ℝ)/42188800)-4 = (1350663:ℝ)/42188800 by norm_num]
    exact paid_terminal_12
  · change terminalPayment 13 ≤ terminalValue ((point cut hi 1024 13+point cut hi 1024 14)/2)
    have hp : terminalPayment 13 = (661436296905:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 13+point cut hi 1024 14)/2 = (170131013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170131013:ℝ)/42188800) = (2704115:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170131013:ℝ)/42188800)-4 = (1375813:ℝ)/42188800 by norm_num]
    exact paid_terminal_13
  · change terminalPayment 14 ≤ terminalValue ((point cut hi 1024 14+point cut hi 1024 15)/2)
    have hp : terminalPayment 14 = (661085159167:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 14+point cut hi 1024 15)/2 = (170156163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170156163:ℝ)/42188800) = (2703109:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170156163:ℝ)/42188800)-4 = (1400963:ℝ)/42188800 by norm_num]
    exact paid_terminal_14
  · change terminalPayment 15 ≤ terminalValue ((point cut hi 1024 15+point cut hi 1024 16)/2)
    have hp : terminalPayment 15 = (660733607773:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 15+point cut hi 1024 16)/2 = (170181313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170181313:ℝ)/42188800) = (2702103:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170181313:ℝ)/42188800)-4 = (1426113:ℝ)/42188800 by norm_num]
    exact paid_terminal_15
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_000
