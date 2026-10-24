import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints035
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_035 (j : Fin 16) : terminalPayment (16*35+j.val) ≤
    terminalValue ((point cut hi 1024 (16*35+j.val)+point cut hi 1024 (16*35+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 560 ≤ terminalValue ((point cut hi 1024 560+point cut hi 1024 561)/2)
    have hp : terminalPayment 560 = (395658208496:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 560+point cut hi 1024 561)/2 = (1785321:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((1785321:ℝ)/409600) = (20911:ℝ)/16384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((1785321:ℝ)/409600)-4 = (146921:ℝ)/409600 by norm_num]
    exact paid_terminal_560
  · change terminalPayment 561 ≤ terminalValue ((point cut hi 1024 561+point cut hi 1024 562)/2)
    have hp : terminalPayment 561 = (395009285441:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 561+point cut hi 1024 562)/2 = (183913213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183913213:ℝ)/42188800) = (2152827:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183913213:ℝ)/42188800)-4 = (15158013:ℝ)/42188800 by norm_num]
    exact paid_terminal_561
  · change terminalPayment 562 ≤ terminalValue ((point cut hi 1024 562+point cut hi 1024 563)/2)
    have hp : terminalPayment 562 = (394359640218:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 562+point cut hi 1024 563)/2 = (183938363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183938363:ℝ)/42188800) = (2151821:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183938363:ℝ)/42188800)-4 = (15183163:ℝ)/42188800 by norm_num]
    exact paid_terminal_562
  · change terminalPayment 563 ≤ terminalValue ((point cut hi 1024 563+point cut hi 1024 564)/2)
    have hp : terminalPayment 563 = (393709271966:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 563+point cut hi 1024 564)/2 = (183963513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183963513:ℝ)/42188800) = (2150815:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183963513:ℝ)/42188800)-4 = (15208313:ℝ)/42188800 by norm_num]
    exact paid_terminal_563
  · change terminalPayment 564 ≤ terminalValue ((point cut hi 1024 564+point cut hi 1024 565)/2)
    have hp : terminalPayment 564 = (393058179825:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 564+point cut hi 1024 565)/2 = (183988663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183988663:ℝ)/42188800) = (2149809:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183988663:ℝ)/42188800)-4 = (15233463:ℝ)/42188800 by norm_num]
    exact paid_terminal_564
  · change terminalPayment 565 ≤ terminalValue ((point cut hi 1024 565+point cut hi 1024 566)/2)
    have hp : terminalPayment 565 = (392406362931:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 565+point cut hi 1024 566)/2 = (184013813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184013813:ℝ)/42188800) = (2148803:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184013813:ℝ)/42188800)-4 = (15258613:ℝ)/42188800 by norm_num]
    exact paid_terminal_565
  · change terminalPayment 566 ≤ terminalValue ((point cut hi 1024 566+point cut hi 1024 567)/2)
    have hp : terminalPayment 566 = (391753820421:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 566+point cut hi 1024 567)/2 = (184038963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184038963:ℝ)/42188800) = (2147797:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184038963:ℝ)/42188800)-4 = (15283763:ℝ)/42188800 by norm_num]
    exact paid_terminal_566
  · change terminalPayment 567 ≤ terminalValue ((point cut hi 1024 567+point cut hi 1024 568)/2)
    have hp : terminalPayment 567 = (391100551428:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 567+point cut hi 1024 568)/2 = (184064113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184064113:ℝ)/42188800) = (2146791:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184064113:ℝ)/42188800)-4 = (15308913:ℝ)/42188800 by norm_num]
    exact paid_terminal_567
  · change terminalPayment 568 ≤ terminalValue ((point cut hi 1024 568+point cut hi 1024 569)/2)
    have hp : terminalPayment 568 = (390446555085:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 568+point cut hi 1024 569)/2 = (184089263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184089263:ℝ)/42188800) = (2145785:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184089263:ℝ)/42188800)-4 = (15334063:ℝ)/42188800 by norm_num]
    exact paid_terminal_568
  · change terminalPayment 569 ≤ terminalValue ((point cut hi 1024 569+point cut hi 1024 570)/2)
    have hp : terminalPayment 569 = (389791830523:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 569+point cut hi 1024 570)/2 = (184114413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184114413:ℝ)/42188800) = (2144779:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184114413:ℝ)/42188800)-4 = (15359213:ℝ)/42188800 by norm_num]
    exact paid_terminal_569
  · change terminalPayment 570 ≤ terminalValue ((point cut hi 1024 570+point cut hi 1024 571)/2)
    have hp : terminalPayment 570 = (389136376874:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 570+point cut hi 1024 571)/2 = (184139563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184139563:ℝ)/42188800) = (2143773:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184139563:ℝ)/42188800)-4 = (15384363:ℝ)/42188800 by norm_num]
    exact paid_terminal_570
  · change terminalPayment 571 ≤ terminalValue ((point cut hi 1024 571+point cut hi 1024 572)/2)
    have hp : terminalPayment 571 = (388480193264:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 571+point cut hi 1024 572)/2 = (184164713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184164713:ℝ)/42188800) = (2142767:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184164713:ℝ)/42188800)-4 = (15409513:ℝ)/42188800 by norm_num]
    exact paid_terminal_571
  · change terminalPayment 572 ≤ terminalValue ((point cut hi 1024 572+point cut hi 1024 573)/2)
    have hp : terminalPayment 572 = (387823278821:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 572+point cut hi 1024 573)/2 = (184189863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184189863:ℝ)/42188800) = (2141761:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184189863:ℝ)/42188800)-4 = (15434663:ℝ)/42188800 by norm_num]
    exact paid_terminal_572
  · change terminalPayment 573 ≤ terminalValue ((point cut hi 1024 573+point cut hi 1024 574)/2)
    have hp : terminalPayment 573 = (387165632671:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 573+point cut hi 1024 574)/2 = (184215013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184215013:ℝ)/42188800) = (2140755:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184215013:ℝ)/42188800)-4 = (15459813:ℝ)/42188800 by norm_num]
    exact paid_terminal_573
  · change terminalPayment 574 ≤ terminalValue ((point cut hi 1024 574+point cut hi 1024 575)/2)
    have hp : terminalPayment 574 = (386507253937:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 574+point cut hi 1024 575)/2 = (184240163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184240163:ℝ)/42188800) = (2139749:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184240163:ℝ)/42188800)-4 = (15484963:ℝ)/42188800 by norm_num]
    exact paid_terminal_574
  · change terminalPayment 575 ≤ terminalValue ((point cut hi 1024 575+point cut hi 1024 576)/2)
    have hp : terminalPayment 575 = (385848141743:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 575+point cut hi 1024 576)/2 = (184265313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184265313:ℝ)/42188800) = (2138743:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184265313:ℝ)/42188800)-4 = (15510113:ℝ)/42188800 by norm_num]
    exact paid_terminal_575
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_035
