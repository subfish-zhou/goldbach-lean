import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints029
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_029 (j : Fin 16) : terminalPayment (16*29+j.val) ≤
    terminalValue ((point cut hi 1024 (16*29+j.val)+point cut hi 1024 (16*29+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 464 ≤ terminalValue ((point cut hi 1024 464+point cut hi 1024 465)/2)
    have hp : terminalPayment 464 = (454717973554:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 464+point cut hi 1024 465)/2 = (181473663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181473663:ℝ)/42188800) = (2250409:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181473663:ℝ)/42188800)-4 = (12718463:ℝ)/42188800 by norm_num]
    exact paid_terminal_464
  · change terminalPayment 465 ≤ terminalValue ((point cut hi 1024 465+point cut hi 1024 466)/2)
    have hp : terminalPayment 465 = (454134584181:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 465+point cut hi 1024 466)/2 = (181498813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181498813:ℝ)/42188800) = (2249403:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181498813:ℝ)/42188800)-4 = (12743613:ℝ)/42188800 by norm_num]
    exact paid_terminal_465
  · change terminalPayment 466 ≤ terminalValue ((point cut hi 1024 466+point cut hi 1024 467)/2)
    have hp : terminalPayment 466 = (453550548871:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 466+point cut hi 1024 467)/2 = (181523963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181523963:ℝ)/42188800) = (2248397:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181523963:ℝ)/42188800)-4 = (12768763:ℝ)/42188800 by norm_num]
    exact paid_terminal_466
  · change terminalPayment 467 ≤ terminalValue ((point cut hi 1024 467+point cut hi 1024 468)/2)
    have hp : terminalPayment 467 = (452965866892:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 467+point cut hi 1024 468)/2 = (181549113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181549113:ℝ)/42188800) = (2247391:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181549113:ℝ)/42188800)-4 = (12793913:ℝ)/42188800 by norm_num]
    exact paid_terminal_467
  · change terminalPayment 468 ≤ terminalValue ((point cut hi 1024 468+point cut hi 1024 469)/2)
    have hp : terminalPayment 468 = (452380537509:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 468+point cut hi 1024 469)/2 = (181574263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181574263:ℝ)/42188800) = (2246385:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181574263:ℝ)/42188800)-4 = (12819063:ℝ)/42188800 by norm_num]
    exact paid_terminal_468
  · change terminalPayment 469 ≤ terminalValue ((point cut hi 1024 469+point cut hi 1024 470)/2)
    have hp : terminalPayment 469 = (451794559987:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 469+point cut hi 1024 470)/2 = (181599413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181599413:ℝ)/42188800) = (2245379:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181599413:ℝ)/42188800)-4 = (12844213:ℝ)/42188800 by norm_num]
    exact paid_terminal_469
  · change terminalPayment 470 ≤ terminalValue ((point cut hi 1024 470+point cut hi 1024 471)/2)
    have hp : terminalPayment 470 = (451207933588:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 470+point cut hi 1024 471)/2 = (181624563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181624563:ℝ)/42188800) = (2244373:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181624563:ℝ)/42188800)-4 = (12869363:ℝ)/42188800 by norm_num]
    exact paid_terminal_470
  · change terminalPayment 471 ≤ terminalValue ((point cut hi 1024 471+point cut hi 1024 472)/2)
    have hp : terminalPayment 471 = (450620657576:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 471+point cut hi 1024 472)/2 = (181649713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181649713:ℝ)/42188800) = (2243367:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181649713:ℝ)/42188800)-4 = (12894513:ℝ)/42188800 by norm_num]
    exact paid_terminal_471
  · change terminalPayment 472 ≤ terminalValue ((point cut hi 1024 472+point cut hi 1024 473)/2)
    have hp : terminalPayment 472 = (450032731210:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 472+point cut hi 1024 473)/2 = (181674863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181674863:ℝ)/42188800) = (2242361:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181674863:ℝ)/42188800)-4 = (12919663:ℝ)/42188800 by norm_num]
    exact paid_terminal_472
  · change terminalPayment 473 ≤ terminalValue ((point cut hi 1024 473+point cut hi 1024 474)/2)
    have hp : terminalPayment 473 = (449444153750:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 473+point cut hi 1024 474)/2 = (181700013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181700013:ℝ)/42188800) = (2241355:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181700013:ℝ)/42188800)-4 = (12944813:ℝ)/42188800 by norm_num]
    exact paid_terminal_473
  · change terminalPayment 474 ≤ terminalValue ((point cut hi 1024 474+point cut hi 1024 475)/2)
    have hp : terminalPayment 474 = (448854924455:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 474+point cut hi 1024 475)/2 = (181725163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181725163:ℝ)/42188800) = (2240349:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181725163:ℝ)/42188800)-4 = (12969963:ℝ)/42188800 by norm_num]
    exact paid_terminal_474
  · change terminalPayment 475 ≤ terminalValue ((point cut hi 1024 475+point cut hi 1024 476)/2)
    have hp : terminalPayment 475 = (448265042581:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 475+point cut hi 1024 476)/2 = (181750313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181750313:ℝ)/42188800) = (2239343:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181750313:ℝ)/42188800)-4 = (12995113:ℝ)/42188800 by norm_num]
    exact paid_terminal_475
  · change terminalPayment 476 ≤ terminalValue ((point cut hi 1024 476+point cut hi 1024 477)/2)
    have hp : terminalPayment 476 = (447674507384:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 476+point cut hi 1024 477)/2 = (181775463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181775463:ℝ)/42188800) = (2238337:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181775463:ℝ)/42188800)-4 = (13020263:ℝ)/42188800 by norm_num]
    exact paid_terminal_476
  · change terminalPayment 477 ≤ terminalValue ((point cut hi 1024 477+point cut hi 1024 478)/2)
    have hp : terminalPayment 477 = (447083318120:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 477+point cut hi 1024 478)/2 = (181800613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181800613:ℝ)/42188800) = (2237331:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181800613:ℝ)/42188800)-4 = (13045413:ℝ)/42188800 by norm_num]
    exact paid_terminal_477
  · change terminalPayment 478 ≤ terminalValue ((point cut hi 1024 478+point cut hi 1024 479)/2)
    have hp : terminalPayment 478 = (446491474040:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 478+point cut hi 1024 479)/2 = (181825763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181825763:ℝ)/42188800) = (2236325:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181825763:ℝ)/42188800)-4 = (13070563:ℝ)/42188800 by norm_num]
    exact paid_terminal_478
  · change terminalPayment 479 ≤ terminalValue ((point cut hi 1024 479+point cut hi 1024 480)/2)
    have hp : terminalPayment 479 = (445898974399:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 479+point cut hi 1024 480)/2 = (181850913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181850913:ℝ)/42188800) = (2235319:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181850913:ℝ)/42188800)-4 = (13095713:ℝ)/42188800 by norm_num]
    exact paid_terminal_479
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_029
