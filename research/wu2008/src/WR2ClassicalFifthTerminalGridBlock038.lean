import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints038
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_038 (j : Fin 16) : terminalPayment (16*38+j.val) ≤
    terminalValue ((point cut hi 1024 (16*38+j.val)+point cut hi 1024 (16*38+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 608 ≤ terminalValue ((point cut hi 1024 608+point cut hi 1024 609)/2)
    have hp : terminalPayment 608 = (363680137410:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 608+point cut hi 1024 609)/2 = (185095263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185095263:ℝ)/42188800) = (2105545:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185095263:ℝ)/42188800)-4 = (16340063:ℝ)/42188800 by norm_num]
    exact paid_terminal_608
  · change terminalPayment 609 ≤ terminalValue ((point cut hi 1024 609+point cut hi 1024 610)/2)
    have hp : terminalPayment 609 = (362995554817:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 609+point cut hi 1024 610)/2 = (185120413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185120413:ℝ)/42188800) = (2104539:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185120413:ℝ)/42188800)-4 = (16365213:ℝ)/42188800 by norm_num]
    exact paid_terminal_609
  · change terminalPayment 610 ≤ terminalValue ((point cut hi 1024 610+point cut hi 1024 611)/2)
    have hp : terminalPayment 610 = (362310207106:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 610+point cut hi 1024 611)/2 = (185145563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185145563:ℝ)/42188800) = (2103533:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185145563:ℝ)/42188800)-4 = (16390363:ℝ)/42188800 by norm_num]
    exact paid_terminal_610
  · change terminalPayment 611 ≤ terminalValue ((point cut hi 1024 611+point cut hi 1024 612)/2)
    have hp : terminalPayment 611 = (361624093346:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 611+point cut hi 1024 612)/2 = (185170713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185170713:ℝ)/42188800) = (2102527:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185170713:ℝ)/42188800)-4 = (16415513:ℝ)/42188800 by norm_num]
    exact paid_terminal_611
  · change terminalPayment 612 ≤ terminalValue ((point cut hi 1024 612+point cut hi 1024 613)/2)
    have hp : terminalPayment 612 = (360937212602:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 612+point cut hi 1024 613)/2 = (185195863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185195863:ℝ)/42188800) = (2101521:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185195863:ℝ)/42188800)-4 = (16440663:ℝ)/42188800 by norm_num]
    exact paid_terminal_612
  · change terminalPayment 613 ≤ terminalValue ((point cut hi 1024 613+point cut hi 1024 614)/2)
    have hp : terminalPayment 613 = (360249563940:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 613+point cut hi 1024 614)/2 = (185221013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185221013:ℝ)/42188800) = (2100515:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185221013:ℝ)/42188800)-4 = (16465813:ℝ)/42188800 by norm_num]
    exact paid_terminal_613
  · change terminalPayment 614 ≤ terminalValue ((point cut hi 1024 614+point cut hi 1024 615)/2)
    have hp : terminalPayment 614 = (359561146423:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 614+point cut hi 1024 615)/2 = (185246163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185246163:ℝ)/42188800) = (2099509:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185246163:ℝ)/42188800)-4 = (16490963:ℝ)/42188800 by norm_num]
    exact paid_terminal_614
  · change terminalPayment 615 ≤ terminalValue ((point cut hi 1024 615+point cut hi 1024 616)/2)
    have hp : terminalPayment 615 = (358871959112:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 615+point cut hi 1024 616)/2 = (185271313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185271313:ℝ)/42188800) = (2098503:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185271313:ℝ)/42188800)-4 = (16516113:ℝ)/42188800 by norm_num]
    exact paid_terminal_615
  · change terminalPayment 616 ≤ terminalValue ((point cut hi 1024 616+point cut hi 1024 617)/2)
    have hp : terminalPayment 616 = (358182001066:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 616+point cut hi 1024 617)/2 = (185296463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185296463:ℝ)/42188800) = (2097497:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185296463:ℝ)/42188800)-4 = (16541263:ℝ)/42188800 by norm_num]
    exact paid_terminal_616
  · change terminalPayment 617 ≤ terminalValue ((point cut hi 1024 617+point cut hi 1024 618)/2)
    have hp : terminalPayment 617 = (357491271346:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 617+point cut hi 1024 618)/2 = (185321613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185321613:ℝ)/42188800) = (2096491:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185321613:ℝ)/42188800)-4 = (16566413:ℝ)/42188800 by norm_num]
    exact paid_terminal_617
  · change terminalPayment 618 ≤ terminalValue ((point cut hi 1024 618+point cut hi 1024 619)/2)
    have hp : terminalPayment 618 = (356799769006:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 618+point cut hi 1024 619)/2 = (185346763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185346763:ℝ)/42188800) = (2095485:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185346763:ℝ)/42188800)-4 = (16591563:ℝ)/42188800 by norm_num]
    exact paid_terminal_618
  · change terminalPayment 619 ≤ terminalValue ((point cut hi 1024 619+point cut hi 1024 620)/2)
    have hp : terminalPayment 619 = (356107493103:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 619+point cut hi 1024 620)/2 = (185371913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185371913:ℝ)/42188800) = (2094479:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185371913:ℝ)/42188800)-4 = (16616713:ℝ)/42188800 by norm_num]
    exact paid_terminal_619
  · change terminalPayment 620 ≤ terminalValue ((point cut hi 1024 620+point cut hi 1024 621)/2)
    have hp : terminalPayment 620 = (355414442690:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 620+point cut hi 1024 621)/2 = (185397063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185397063:ℝ)/42188800) = (2093473:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185397063:ℝ)/42188800)-4 = (16641863:ℝ)/42188800 by norm_num]
    exact paid_terminal_620
  · change terminalPayment 621 ≤ terminalValue ((point cut hi 1024 621+point cut hi 1024 622)/2)
    have hp : terminalPayment 621 = (354720616819:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 621+point cut hi 1024 622)/2 = (185422213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185422213:ℝ)/42188800) = (2092467:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185422213:ℝ)/42188800)-4 = (16667013:ℝ)/42188800 by norm_num]
    exact paid_terminal_621
  · change terminalPayment 622 ≤ terminalValue ((point cut hi 1024 622+point cut hi 1024 623)/2)
    have hp : terminalPayment 622 = (354026014539:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 622+point cut hi 1024 623)/2 = (185447363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185447363:ℝ)/42188800) = (2091461:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185447363:ℝ)/42188800)-4 = (16692163:ℝ)/42188800 by norm_num]
    exact paid_terminal_622
  · change terminalPayment 623 ≤ terminalValue ((point cut hi 1024 623+point cut hi 1024 624)/2)
    have hp : terminalPayment 623 = (353330634901:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 623+point cut hi 1024 624)/2 = (185472513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185472513:ℝ)/42188800) = (2090455:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185472513:ℝ)/42188800)-4 = (16717313:ℝ)/42188800 by norm_num]
    exact paid_terminal_623
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_038
