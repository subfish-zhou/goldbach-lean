import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints026
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_026 (j : Fin 16) : terminalPayment (16*26+j.val) ≤
    terminalValue ((point cut hi 1024 (16*26+j.val)+point cut hi 1024 (16*26+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 416 ≤ terminalValue ((point cut hi 1024 416+point cut hi 1024 417)/2)
    have hp : terminalPayment 416 = (481975114441:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 416+point cut hi 1024 417)/2 = (180266463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180266463:ℝ)/42188800) = (2298697:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180266463:ℝ)/42188800)-4 = (11511263:ℝ)/42188800 by norm_num]
    exact paid_terminal_416
  · change terminalPayment 417 ≤ terminalValue ((point cut hi 1024 417+point cut hi 1024 418)/2)
    have hp : terminalPayment 417 = (481421891083:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 417+point cut hi 1024 418)/2 = (180291613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180291613:ℝ)/42188800) = (2297691:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180291613:ℝ)/42188800)-4 = (11536413:ℝ)/42188800 by norm_num]
    exact paid_terminal_417
  · change terminalPayment 418 ≤ terminalValue ((point cut hi 1024 418+point cut hi 1024 419)/2)
    have hp : terminalPayment 418 = (480868055594:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 418+point cut hi 1024 419)/2 = (180316763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180316763:ℝ)/42188800) = (2296685:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180316763:ℝ)/42188800)-4 = (11561563:ℝ)/42188800 by norm_num]
    exact paid_terminal_418
  · change terminalPayment 419 ≤ terminalValue ((point cut hi 1024 419+point cut hi 1024 420)/2)
    have hp : terminalPayment 419 = (480313607296:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 419+point cut hi 1024 420)/2 = (180341913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180341913:ℝ)/42188800) = (2295679:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180341913:ℝ)/42188800)-4 = (11586713:ℝ)/42188800 by norm_num]
    exact paid_terminal_419
  · change terminalPayment 420 ≤ terminalValue ((point cut hi 1024 420+point cut hi 1024 421)/2)
    have hp : terminalPayment 420 = (479758545511:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 420+point cut hi 1024 421)/2 = (180367063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180367063:ℝ)/42188800) = (2294673:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180367063:ℝ)/42188800)-4 = (11611863:ℝ)/42188800 by norm_num]
    exact paid_terminal_420
  · change terminalPayment 421 ≤ terminalValue ((point cut hi 1024 421+point cut hi 1024 422)/2)
    have hp : terminalPayment 421 = (479202869559:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 421+point cut hi 1024 422)/2 = (180392213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180392213:ℝ)/42188800) = (2293667:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180392213:ℝ)/42188800)-4 = (11637013:ℝ)/42188800 by norm_num]
    exact paid_terminal_421
  · change terminalPayment 422 ≤ terminalValue ((point cut hi 1024 422+point cut hi 1024 423)/2)
    have hp : terminalPayment 422 = (478646578759:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 422+point cut hi 1024 423)/2 = (180417363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180417363:ℝ)/42188800) = (2292661:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180417363:ℝ)/42188800)-4 = (11662163:ℝ)/42188800 by norm_num]
    exact paid_terminal_422
  · change terminalPayment 423 ≤ terminalValue ((point cut hi 1024 423+point cut hi 1024 424)/2)
    have hp : terminalPayment 423 = (478089672431:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 423+point cut hi 1024 424)/2 = (180442513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180442513:ℝ)/42188800) = (2291655:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180442513:ℝ)/42188800)-4 = (11687313:ℝ)/42188800 by norm_num]
    exact paid_terminal_423
  · change terminalPayment 424 ≤ terminalValue ((point cut hi 1024 424+point cut hi 1024 425)/2)
    have hp : terminalPayment 424 = (477532149891:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 424+point cut hi 1024 425)/2 = (180467663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180467663:ℝ)/42188800) = (2290649:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180467663:ℝ)/42188800)-4 = (11712463:ℝ)/42188800 by norm_num]
    exact paid_terminal_424
  · change terminalPayment 425 ≤ terminalValue ((point cut hi 1024 425+point cut hi 1024 426)/2)
    have hp : terminalPayment 425 = (476974010454:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 425+point cut hi 1024 426)/2 = (180492813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180492813:ℝ)/42188800) = (2289643:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180492813:ℝ)/42188800)-4 = (11737613:ℝ)/42188800 by norm_num]
    exact paid_terminal_425
  · change terminalPayment 426 ≤ terminalValue ((point cut hi 1024 426+point cut hi 1024 427)/2)
    have hp : terminalPayment 426 = (476415253436:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 426+point cut hi 1024 427)/2 = (180517963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180517963:ℝ)/42188800) = (2288637:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180517963:ℝ)/42188800)-4 = (11762763:ℝ)/42188800 by norm_num]
    exact paid_terminal_426
  · change terminalPayment 427 ≤ terminalValue ((point cut hi 1024 427+point cut hi 1024 428)/2)
    have hp : terminalPayment 427 = (475855878150:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 427+point cut hi 1024 428)/2 = (180543113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180543113:ℝ)/42188800) = (2287631:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180543113:ℝ)/42188800)-4 = (11787913:ℝ)/42188800 by norm_num]
    exact paid_terminal_427
  · change terminalPayment 428 ≤ terminalValue ((point cut hi 1024 428+point cut hi 1024 429)/2)
    have hp : terminalPayment 428 = (475295883910:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 428+point cut hi 1024 429)/2 = (180568263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180568263:ℝ)/42188800) = (2286625:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180568263:ℝ)/42188800)-4 = (11813063:ℝ)/42188800 by norm_num]
    exact paid_terminal_428
  · change terminalPayment 429 ≤ terminalValue ((point cut hi 1024 429+point cut hi 1024 430)/2)
    have hp : terminalPayment 429 = (474735270026:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 429+point cut hi 1024 430)/2 = (180593413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180593413:ℝ)/42188800) = (2285619:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180593413:ℝ)/42188800)-4 = (11838213:ℝ)/42188800 by norm_num]
    exact paid_terminal_429
  · change terminalPayment 430 ≤ terminalValue ((point cut hi 1024 430+point cut hi 1024 431)/2)
    have hp : terminalPayment 430 = (474174035808:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 430+point cut hi 1024 431)/2 = (180618563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180618563:ℝ)/42188800) = (2284613:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180618563:ℝ)/42188800)-4 = (11863363:ℝ)/42188800 by norm_num]
    exact paid_terminal_430
  · change terminalPayment 431 ≤ terminalValue ((point cut hi 1024 431+point cut hi 1024 432)/2)
    have hp : terminalPayment 431 = (473612180567:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 431+point cut hi 1024 432)/2 = (180643713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180643713:ℝ)/42188800) = (2283607:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180643713:ℝ)/42188800)-4 = (11888513:ℝ)/42188800 by norm_num]
    exact paid_terminal_431
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_026
