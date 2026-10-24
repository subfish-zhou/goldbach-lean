import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints037
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_037 (j : Fin 16) : terminalPayment (16*37+j.val) ≤
    terminalValue ((point cut hi 1024 (16*37+j.val)+point cut hi 1024 (16*37+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 592 ≤ terminalValue ((point cut hi 1024 592+point cut hi 1024 593)/2)
    have hp : terminalPayment 592 = (374530157545:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 592+point cut hi 1024 593)/2 = (184692863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184692863:ℝ)/42188800) = (2121641:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184692863:ℝ)/42188800)-4 = (15937663:ℝ)/42188800 by norm_num]
    exact paid_terminal_592
  · change terminalPayment 593 ≤ terminalValue ((point cut hi 1024 593+point cut hi 1024 594)/2)
    have hp : terminalPayment 593 = (373857691327:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 593+point cut hi 1024 594)/2 = (184718013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184718013:ℝ)/42188800) = (2120635:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184718013:ℝ)/42188800)-4 = (15962813:ℝ)/42188800 by norm_num]
    exact paid_terminal_593
  · change terminalPayment 594 ≤ terminalValue ((point cut hi 1024 594+point cut hi 1024 595)/2)
    have hp : terminalPayment 594 = (373184474695:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 594+point cut hi 1024 595)/2 = (184743163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184743163:ℝ)/42188800) = (2119629:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184743163:ℝ)/42188800)-4 = (15987963:ℝ)/42188800 by norm_num]
    exact paid_terminal_594
  · change terminalPayment 595 ≤ terminalValue ((point cut hi 1024 595+point cut hi 1024 596)/2)
    have hp : terminalPayment 595 = (372510506741:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 595+point cut hi 1024 596)/2 = (184768313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184768313:ℝ)/42188800) = (2118623:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184768313:ℝ)/42188800)-4 = (16013113:ℝ)/42188800 by norm_num]
    exact paid_terminal_595
  · change terminalPayment 596 ≤ terminalValue ((point cut hi 1024 596+point cut hi 1024 597)/2)
    have hp : terminalPayment 596 = (371835786556:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 596+point cut hi 1024 597)/2 = (184793463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184793463:ℝ)/42188800) = (2117617:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184793463:ℝ)/42188800)-4 = (16038263:ℝ)/42188800 by norm_num]
    exact paid_terminal_596
  · change terminalPayment 597 ≤ terminalValue ((point cut hi 1024 597+point cut hi 1024 598)/2)
    have hp : terminalPayment 597 = (371160313230:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 597+point cut hi 1024 598)/2 = (184818613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184818613:ℝ)/42188800) = (2116611:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184818613:ℝ)/42188800)-4 = (16063413:ℝ)/42188800 by norm_num]
    exact paid_terminal_597
  · change terminalPayment 598 ≤ terminalValue ((point cut hi 1024 598+point cut hi 1024 599)/2)
    have hp : terminalPayment 598 = (370484085851:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 598+point cut hi 1024 599)/2 = (184843763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184843763:ℝ)/42188800) = (2115605:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184843763:ℝ)/42188800)-4 = (16088563:ℝ)/42188800 by norm_num]
    exact paid_terminal_598
  · change terminalPayment 599 ≤ terminalValue ((point cut hi 1024 599+point cut hi 1024 600)/2)
    have hp : terminalPayment 599 = (369807103506:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 599+point cut hi 1024 600)/2 = (184868913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184868913:ℝ)/42188800) = (2114599:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184868913:ℝ)/42188800)-4 = (16113713:ℝ)/42188800 by norm_num]
    exact paid_terminal_599
  · change terminalPayment 600 ≤ terminalValue ((point cut hi 1024 600+point cut hi 1024 601)/2)
    have hp : terminalPayment 600 = (369129365279:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 600+point cut hi 1024 601)/2 = (184894063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184894063:ℝ)/42188800) = (2113593:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184894063:ℝ)/42188800)-4 = (16138863:ℝ)/42188800 by norm_num]
    exact paid_terminal_600
  · change terminalPayment 601 ≤ terminalValue ((point cut hi 1024 601+point cut hi 1024 602)/2)
    have hp : terminalPayment 601 = (368450870254:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 601+point cut hi 1024 602)/2 = (184919213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184919213:ℝ)/42188800) = (2112587:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184919213:ℝ)/42188800)-4 = (16164013:ℝ)/42188800 by norm_num]
    exact paid_terminal_601
  · change terminalPayment 602 ≤ terminalValue ((point cut hi 1024 602+point cut hi 1024 603)/2)
    have hp : terminalPayment 602 = (367771617512:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 602+point cut hi 1024 603)/2 = (184944363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184944363:ℝ)/42188800) = (2111581:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184944363:ℝ)/42188800)-4 = (16189163:ℝ)/42188800 by norm_num]
    exact paid_terminal_602
  · change terminalPayment 603 ≤ terminalValue ((point cut hi 1024 603+point cut hi 1024 604)/2)
    have hp : terminalPayment 603 = (367091606135:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 603+point cut hi 1024 604)/2 = (184969513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184969513:ℝ)/42188800) = (2110575:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184969513:ℝ)/42188800)-4 = (16214313:ℝ)/42188800 by norm_num]
    exact paid_terminal_603
  · change terminalPayment 604 ≤ terminalValue ((point cut hi 1024 604+point cut hi 1024 605)/2)
    have hp : terminalPayment 604 = (366410835200:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 604+point cut hi 1024 605)/2 = (184994663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184994663:ℝ)/42188800) = (2109569:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184994663:ℝ)/42188800)-4 = (16239463:ℝ)/42188800 by norm_num]
    exact paid_terminal_604
  · change terminalPayment 605 ≤ terminalValue ((point cut hi 1024 605+point cut hi 1024 606)/2)
    have hp : terminalPayment 605 = (365729303785:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 605+point cut hi 1024 606)/2 = (185019813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185019813:ℝ)/42188800) = (2108563:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185019813:ℝ)/42188800)-4 = (16264613:ℝ)/42188800 by norm_num]
    exact paid_terminal_605
  · change terminalPayment 606 ≤ terminalValue ((point cut hi 1024 606+point cut hi 1024 607)/2)
    have hp : terminalPayment 606 = (365047010966:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 606+point cut hi 1024 607)/2 = (185044963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185044963:ℝ)/42188800) = (2107557:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185044963:ℝ)/42188800)-4 = (16289763:ℝ)/42188800 by norm_num]
    exact paid_terminal_606
  · change terminalPayment 607 ≤ terminalValue ((point cut hi 1024 607+point cut hi 1024 608)/2)
    have hp : terminalPayment 607 = (364363955817:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 607+point cut hi 1024 608)/2 = (185070113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185070113:ℝ)/42188800) = (2106551:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185070113:ℝ)/42188800)-4 = (16314913:ℝ)/42188800 by norm_num]
    exact paid_terminal_607
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_037
