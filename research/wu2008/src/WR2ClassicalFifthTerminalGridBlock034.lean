import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints034
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_034 (j : Fin 16) : terminalPayment (16*34+j.val) ≤
    terminalValue ((point cut hi 1024 (16*34+j.val)+point cut hi 1024 (16*34+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 544 ≤ terminalValue ((point cut hi 1024 544+point cut hi 1024 545)/2)
    have hp : terminalPayment 544 = (405943458661:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 544+point cut hi 1024 545)/2 = (183485663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183485663:ℝ)/42188800) = (2169929:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183485663:ℝ)/42188800)-4 = (14730463:ℝ)/42188800 by norm_num]
    exact paid_terminal_544
  · change terminalPayment 545 ≤ terminalValue ((point cut hi 1024 545+point cut hi 1024 546)/2)
    have hp : terminalPayment 545 = (405305974510:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 545+point cut hi 1024 546)/2 = (183510813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183510813:ℝ)/42188800) = (2168923:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183510813:ℝ)/42188800)-4 = (14755613:ℝ)/42188800 by norm_num]
    exact paid_terminal_545
  · change terminalPayment 546 ≤ terminalValue ((point cut hi 1024 546+point cut hi 1024 547)/2)
    have hp : terminalPayment 546 = (404667781757:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 546+point cut hi 1024 547)/2 = (183535963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183535963:ℝ)/42188800) = (2167917:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183535963:ℝ)/42188800)-4 = (14780763:ℝ)/42188800 by norm_num]
    exact paid_terminal_546
  · change terminalPayment 547 ≤ terminalValue ((point cut hi 1024 547+point cut hi 1024 548)/2)
    have hp : terminalPayment 547 = (404028879564:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 547+point cut hi 1024 548)/2 = (183561113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183561113:ℝ)/42188800) = (2166911:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183561113:ℝ)/42188800)-4 = (14805913:ℝ)/42188800 by norm_num]
    exact paid_terminal_547
  · change terminalPayment 548 ≤ terminalValue ((point cut hi 1024 548+point cut hi 1024 549)/2)
    have hp : terminalPayment 548 = (403389267092:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 548+point cut hi 1024 549)/2 = (183586263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183586263:ℝ)/42188800) = (2165905:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183586263:ℝ)/42188800)-4 = (14831063:ℝ)/42188800 by norm_num]
    exact paid_terminal_548
  · change terminalPayment 549 ≤ terminalValue ((point cut hi 1024 549+point cut hi 1024 550)/2)
    have hp : terminalPayment 549 = (402748943501:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 549+point cut hi 1024 550)/2 = (183611413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183611413:ℝ)/42188800) = (2164899:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183611413:ℝ)/42188800)-4 = (14856213:ℝ)/42188800 by norm_num]
    exact paid_terminal_549
  · change terminalPayment 550 ≤ terminalValue ((point cut hi 1024 550+point cut hi 1024 551)/2)
    have hp : terminalPayment 550 = (402107907950:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 550+point cut hi 1024 551)/2 = (183636563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183636563:ℝ)/42188800) = (2163893:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183636563:ℝ)/42188800)-4 = (14881363:ℝ)/42188800 by norm_num]
    exact paid_terminal_550
  · change terminalPayment 551 ≤ terminalValue ((point cut hi 1024 551+point cut hi 1024 552)/2)
    have hp : terminalPayment 551 = (401466159596:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 551+point cut hi 1024 552)/2 = (183661713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183661713:ℝ)/42188800) = (2162887:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183661713:ℝ)/42188800)-4 = (14906513:ℝ)/42188800 by norm_num]
    exact paid_terminal_551
  · change terminalPayment 552 ≤ terminalValue ((point cut hi 1024 552+point cut hi 1024 553)/2)
    have hp : terminalPayment 552 = (400823697595:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 552+point cut hi 1024 553)/2 = (183686863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183686863:ℝ)/42188800) = (2161881:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183686863:ℝ)/42188800)-4 = (14931663:ℝ)/42188800 by norm_num]
    exact paid_terminal_552
  · change terminalPayment 553 ≤ terminalValue ((point cut hi 1024 553+point cut hi 1024 554)/2)
    have hp : terminalPayment 553 = (400180521101:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 553+point cut hi 1024 554)/2 = (183712013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183712013:ℝ)/42188800) = (2160875:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183712013:ℝ)/42188800)-4 = (14956813:ℝ)/42188800 by norm_num]
    exact paid_terminal_553
  · change terminalPayment 554 ≤ terminalValue ((point cut hi 1024 554+point cut hi 1024 555)/2)
    have hp : terminalPayment 554 = (399536629266:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 554+point cut hi 1024 555)/2 = (183737163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183737163:ℝ)/42188800) = (2159869:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183737163:ℝ)/42188800)-4 = (14981963:ℝ)/42188800 by norm_num]
    exact paid_terminal_554
  · change terminalPayment 555 ≤ terminalValue ((point cut hi 1024 555+point cut hi 1024 556)/2)
    have hp : terminalPayment 555 = (398892021242:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 555+point cut hi 1024 556)/2 = (183762313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183762313:ℝ)/42188800) = (2158863:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183762313:ℝ)/42188800)-4 = (15007113:ℝ)/42188800 by norm_num]
    exact paid_terminal_555
  · change terminalPayment 556 ≤ terminalValue ((point cut hi 1024 556+point cut hi 1024 557)/2)
    have hp : terminalPayment 556 = (398246696180:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 556+point cut hi 1024 557)/2 = (183787463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183787463:ℝ)/42188800) = (2157857:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183787463:ℝ)/42188800)-4 = (15032263:ℝ)/42188800 by norm_num]
    exact paid_terminal_556
  · change terminalPayment 557 ≤ terminalValue ((point cut hi 1024 557+point cut hi 1024 558)/2)
    have hp : terminalPayment 557 = (397600653228:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 557+point cut hi 1024 558)/2 = (183812613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183812613:ℝ)/42188800) = (2156851:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183812613:ℝ)/42188800)-4 = (15057413:ℝ)/42188800 by norm_num]
    exact paid_terminal_557
  · change terminalPayment 558 ≤ terminalValue ((point cut hi 1024 558+point cut hi 1024 559)/2)
    have hp : terminalPayment 558 = (396953891533:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 558+point cut hi 1024 559)/2 = (183837763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183837763:ℝ)/42188800) = (2155845:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183837763:ℝ)/42188800)-4 = (15082563:ℝ)/42188800 by norm_num]
    exact paid_terminal_558
  · change terminalPayment 559 ≤ terminalValue ((point cut hi 1024 559+point cut hi 1024 560)/2)
    have hp : terminalPayment 559 = (396306410241:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 559+point cut hi 1024 560)/2 = (183862913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183862913:ℝ)/42188800) = (2154839:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183862913:ℝ)/42188800)-4 = (15107713:ℝ)/42188800 by norm_num]
    exact paid_terminal_559
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_034
