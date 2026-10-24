import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints030
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_030 (j : Fin 16) : terminalPayment (16*30+j.val) ≤
    terminalValue ((point cut hi 1024 (16*30+j.val)+point cut hi 1024 (16*30+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 480 ≤ terminalValue ((point cut hi 1024 480+point cut hi 1024 481)/2)
    have hp : terminalPayment 480 = (445305818446:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 480+point cut hi 1024 481)/2 = (181876063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181876063:ℝ)/42188800) = (2234313:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181876063:ℝ)/42188800)-4 = (13120863:ℝ)/42188800 by norm_num]
    exact paid_terminal_480
  · change terminalPayment 481 ≤ terminalValue ((point cut hi 1024 481+point cut hi 1024 482)/2)
    have hp : terminalPayment 481 = (444712005431:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 481+point cut hi 1024 482)/2 = (181901213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181901213:ℝ)/42188800) = (2233307:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181901213:ℝ)/42188800)-4 = (13146013:ℝ)/42188800 by norm_num]
    exact paid_terminal_481
  · change terminalPayment 482 ≤ terminalValue ((point cut hi 1024 482+point cut hi 1024 483)/2)
    have hp : terminalPayment 482 = (444117534602:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 482+point cut hi 1024 483)/2 = (181926363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181926363:ℝ)/42188800) = (2232301:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181926363:ℝ)/42188800)-4 = (13171163:ℝ)/42188800 by norm_num]
    exact paid_terminal_482
  · change terminalPayment 483 ≤ terminalValue ((point cut hi 1024 483+point cut hi 1024 484)/2)
    have hp : terminalPayment 483 = (443522405207:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 483+point cut hi 1024 484)/2 = (181951513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181951513:ℝ)/42188800) = (2231295:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181951513:ℝ)/42188800)-4 = (13196313:ℝ)/42188800 by norm_num]
    exact paid_terminal_483
  · change terminalPayment 484 ≤ terminalValue ((point cut hi 1024 484+point cut hi 1024 485)/2)
    have hp : terminalPayment 484 = (442926616492:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 484+point cut hi 1024 485)/2 = (181976663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181976663:ℝ)/42188800) = (2230289:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181976663:ℝ)/42188800)-4 = (13221463:ℝ)/42188800 by norm_num]
    exact paid_terminal_484
  · change terminalPayment 485 ≤ terminalValue ((point cut hi 1024 485+point cut hi 1024 486)/2)
    have hp : terminalPayment 485 = (442330167701:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 485+point cut hi 1024 486)/2 = (182001813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182001813:ℝ)/42188800) = (2229283:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182001813:ℝ)/42188800)-4 = (13246613:ℝ)/42188800 by norm_num]
    exact paid_terminal_485
  · change terminalPayment 486 ≤ terminalValue ((point cut hi 1024 486+point cut hi 1024 487)/2)
    have hp : terminalPayment 486 = (441733058078:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 486+point cut hi 1024 487)/2 = (182026963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182026963:ℝ)/42188800) = (2228277:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182026963:ℝ)/42188800)-4 = (13271763:ℝ)/42188800 by norm_num]
    exact paid_terminal_486
  · change terminalPayment 487 ≤ terminalValue ((point cut hi 1024 487+point cut hi 1024 488)/2)
    have hp : terminalPayment 487 = (441135286866:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 487+point cut hi 1024 488)/2 = (182052113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182052113:ℝ)/42188800) = (2227271:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182052113:ℝ)/42188800)-4 = (13296913:ℝ)/42188800 by norm_num]
    exact paid_terminal_487
  · change terminalPayment 488 ≤ terminalValue ((point cut hi 1024 488+point cut hi 1024 489)/2)
    have hp : terminalPayment 488 = (440536853303:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 488+point cut hi 1024 489)/2 = (182077263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182077263:ℝ)/42188800) = (2226265:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182077263:ℝ)/42188800)-4 = (13322063:ℝ)/42188800 by norm_num]
    exact paid_terminal_488
  · change terminalPayment 489 ≤ terminalValue ((point cut hi 1024 489+point cut hi 1024 490)/2)
    have hp : terminalPayment 489 = (439937756632:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 489+point cut hi 1024 490)/2 = (182102413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182102413:ℝ)/42188800) = (2225259:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182102413:ℝ)/42188800)-4 = (13347213:ℝ)/42188800 by norm_num]
    exact paid_terminal_489
  · change terminalPayment 490 ≤ terminalValue ((point cut hi 1024 490+point cut hi 1024 491)/2)
    have hp : terminalPayment 490 = (439337996089:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 490+point cut hi 1024 491)/2 = (182127563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182127563:ℝ)/42188800) = (2224253:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182127563:ℝ)/42188800)-4 = (13372363:ℝ)/42188800 by norm_num]
    exact paid_terminal_490
  · change terminalPayment 491 ≤ terminalValue ((point cut hi 1024 491+point cut hi 1024 492)/2)
    have hp : terminalPayment 491 = (438737570913:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 491+point cut hi 1024 492)/2 = (182152713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182152713:ℝ)/42188800) = (2223247:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182152713:ℝ)/42188800)-4 = (13397513:ℝ)/42188800 by norm_num]
    exact paid_terminal_491
  · change terminalPayment 492 ≤ terminalValue ((point cut hi 1024 492+point cut hi 1024 493)/2)
    have hp : terminalPayment 492 = (438136480339:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 492+point cut hi 1024 493)/2 = (182177863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182177863:ℝ)/42188800) = (2222241:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182177863:ℝ)/42188800)-4 = (13422663:ℝ)/42188800 by norm_num]
    exact paid_terminal_492
  · change terminalPayment 493 ≤ terminalValue ((point cut hi 1024 493+point cut hi 1024 494)/2)
    have hp : terminalPayment 493 = (437534723601:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 493+point cut hi 1024 494)/2 = (182203013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182203013:ℝ)/42188800) = (2221235:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182203013:ℝ)/42188800)-4 = (13447813:ℝ)/42188800 by norm_num]
    exact paid_terminal_493
  · change terminalPayment 494 ≤ terminalValue ((point cut hi 1024 494+point cut hi 1024 495)/2)
    have hp : terminalPayment 494 = (436932299933:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 494+point cut hi 1024 495)/2 = (182228163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182228163:ℝ)/42188800) = (2220229:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182228163:ℝ)/42188800)-4 = (13472963:ℝ)/42188800 by norm_num]
    exact paid_terminal_494
  · change terminalPayment 495 ≤ terminalValue ((point cut hi 1024 495+point cut hi 1024 496)/2)
    have hp : terminalPayment 495 = (436329208567:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 495+point cut hi 1024 496)/2 = (182253313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182253313:ℝ)/42188800) = (2219223:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182253313:ℝ)/42188800)-4 = (13498113:ℝ)/42188800 by norm_num]
    exact paid_terminal_495
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_030
