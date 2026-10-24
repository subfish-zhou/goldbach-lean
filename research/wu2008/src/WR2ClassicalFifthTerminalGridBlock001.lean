import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints001
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_001 (j : Fin 16) : terminalPayment (16*1+j.val) ≤
    terminalValue ((point cut hi 1024 (16*1+j.val)+point cut hi 1024 (16*1+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 16 ≤ terminalValue ((point cut hi 1024 16+point cut hi 1024 17)/2)
    have hp : terminalPayment 16 = (660381642382:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 16+point cut hi 1024 17)/2 = (170206463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170206463:ℝ)/42188800) = (2701097:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170206463:ℝ)/42188800)-4 = (1451263:ℝ)/42188800 by norm_num]
    exact paid_terminal_16
  · change terminalPayment 17 ≤ terminalValue ((point cut hi 1024 17+point cut hi 1024 18)/2)
    have hp : terminalPayment 17 = (660029262653:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 17+point cut hi 1024 18)/2 = (170231613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170231613:ℝ)/42188800) = (2700091:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170231613:ℝ)/42188800)-4 = (1476413:ℝ)/42188800 by norm_num]
    exact paid_terminal_17
  · change terminalPayment 18 ≤ terminalValue ((point cut hi 1024 18+point cut hi 1024 19)/2)
    have hp : terminalPayment 18 = (659676468245:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 18+point cut hi 1024 19)/2 = (170256763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170256763:ℝ)/42188800) = (2699085:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170256763:ℝ)/42188800)-4 = (1501563:ℝ)/42188800 by norm_num]
    exact paid_terminal_18
  · change terminalPayment 19 ≤ terminalValue ((point cut hi 1024 19+point cut hi 1024 20)/2)
    have hp : terminalPayment 19 = (659323258815:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 19+point cut hi 1024 20)/2 = (170281913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170281913:ℝ)/42188800) = (2698079:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170281913:ℝ)/42188800)-4 = (1526713:ℝ)/42188800 by norm_num]
    exact paid_terminal_19
  · change terminalPayment 20 ≤ terminalValue ((point cut hi 1024 20+point cut hi 1024 21)/2)
    have hp : terminalPayment 20 = (658969634020:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 20+point cut hi 1024 21)/2 = (170307063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170307063:ℝ)/42188800) = (2697073:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170307063:ℝ)/42188800)-4 = (1551863:ℝ)/42188800 by norm_num]
    exact paid_terminal_20
  · change terminalPayment 21 ≤ terminalValue ((point cut hi 1024 21+point cut hi 1024 22)/2)
    have hp : terminalPayment 21 = (658615593516:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 21+point cut hi 1024 22)/2 = (170332213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170332213:ℝ)/42188800) = (2696067:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170332213:ℝ)/42188800)-4 = (1577013:ℝ)/42188800 by norm_num]
    exact paid_terminal_21
  · change terminalPayment 22 ≤ terminalValue ((point cut hi 1024 22+point cut hi 1024 23)/2)
    have hp : terminalPayment 22 = (658261136958:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 22+point cut hi 1024 23)/2 = (170357363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170357363:ℝ)/42188800) = (2695061:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170357363:ℝ)/42188800)-4 = (1602163:ℝ)/42188800 by norm_num]
    exact paid_terminal_22
  · change terminalPayment 23 ≤ terminalValue ((point cut hi 1024 23+point cut hi 1024 24)/2)
    have hp : terminalPayment 23 = (657906264002:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 23+point cut hi 1024 24)/2 = (170382513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170382513:ℝ)/42188800) = (2694055:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170382513:ℝ)/42188800)-4 = (1627313:ℝ)/42188800 by norm_num]
    exact paid_terminal_23
  · change terminalPayment 24 ≤ terminalValue ((point cut hi 1024 24+point cut hi 1024 25)/2)
    have hp : terminalPayment 24 = (657550974302:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 24+point cut hi 1024 25)/2 = (170407663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170407663:ℝ)/42188800) = (2693049:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170407663:ℝ)/42188800)-4 = (1652463:ℝ)/42188800 by norm_num]
    exact paid_terminal_24
  · change terminalPayment 25 ≤ terminalValue ((point cut hi 1024 25+point cut hi 1024 26)/2)
    have hp : terminalPayment 25 = (657195267512:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 25+point cut hi 1024 26)/2 = (170432813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170432813:ℝ)/42188800) = (2692043:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170432813:ℝ)/42188800)-4 = (1677613:ℝ)/42188800 by norm_num]
    exact paid_terminal_25
  · change terminalPayment 26 ≤ terminalValue ((point cut hi 1024 26+point cut hi 1024 27)/2)
    have hp : terminalPayment 26 = (656839143284:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 26+point cut hi 1024 27)/2 = (170457963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170457963:ℝ)/42188800) = (2691037:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170457963:ℝ)/42188800)-4 = (1702763:ℝ)/42188800 by norm_num]
    exact paid_terminal_26
  · change terminalPayment 27 ≤ terminalValue ((point cut hi 1024 27+point cut hi 1024 28)/2)
    have hp : terminalPayment 27 = (656482601271:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 27+point cut hi 1024 28)/2 = (170483113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170483113:ℝ)/42188800) = (2690031:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170483113:ℝ)/42188800)-4 = (1727913:ℝ)/42188800 by norm_num]
    exact paid_terminal_27
  · change terminalPayment 28 ≤ terminalValue ((point cut hi 1024 28+point cut hi 1024 29)/2)
    have hp : terminalPayment 28 = (656125641125:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 28+point cut hi 1024 29)/2 = (170508263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170508263:ℝ)/42188800) = (2689025:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170508263:ℝ)/42188800)-4 = (1753063:ℝ)/42188800 by norm_num]
    exact paid_terminal_28
  · change terminalPayment 29 ≤ terminalValue ((point cut hi 1024 29+point cut hi 1024 30)/2)
    have hp : terminalPayment 29 = (655768262497:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 29+point cut hi 1024 30)/2 = (170533413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170533413:ℝ)/42188800) = (2688019:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170533413:ℝ)/42188800)-4 = (1778213:ℝ)/42188800 by norm_num]
    exact paid_terminal_29
  · change terminalPayment 30 ≤ terminalValue ((point cut hi 1024 30+point cut hi 1024 31)/2)
    have hp : terminalPayment 30 = (655410465037:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 30+point cut hi 1024 31)/2 = (170558563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170558563:ℝ)/42188800) = (2687013:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170558563:ℝ)/42188800)-4 = (1803363:ℝ)/42188800 by norm_num]
    exact paid_terminal_30
  · change terminalPayment 31 ≤ terminalValue ((point cut hi 1024 31+point cut hi 1024 32)/2)
    have hp : terminalPayment 31 = (655052248395:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 31+point cut hi 1024 32)/2 = (170583713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170583713:ℝ)/42188800) = (2686007:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170583713:ℝ)/42188800)-4 = (1828513:ℝ)/42188800 by norm_num]
    exact paid_terminal_31
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_001
