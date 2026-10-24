import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints028
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_028 (j : Fin 16) : terminalPayment (16*28+j.val) ≤
    terminalValue ((point cut hi 1024 (16*28+j.val)+point cut hi 1024 (16*28+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 448 ≤ terminalValue ((point cut hi 1024 448+point cut hi 1024 449)/2)
    have hp : terminalPayment 448 = (463964949781:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 448+point cut hi 1024 449)/2 = (181071263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181071263:ℝ)/42188800) = (2266505:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181071263:ℝ)/42188800)-4 = (12316063:ℝ)/42188800 by norm_num]
    exact paid_terminal_448
  · change terminalPayment 449 ≤ terminalValue ((point cut hi 1024 449+point cut hi 1024 450)/2)
    have hp : terminalPayment 449 = (463391796660:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 449+point cut hi 1024 450)/2 = (181096413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181096413:ℝ)/42188800) = (2265499:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181096413:ℝ)/42188800)-4 = (12341213:ℝ)/42188800 by norm_num]
    exact paid_terminal_449
  · change terminalPayment 450 ≤ terminalValue ((point cut hi 1024 450+point cut hi 1024 451)/2)
    have hp : terminalPayment 450 = (462818009171:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 450+point cut hi 1024 451)/2 = (181121563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181121563:ℝ)/42188800) = (2264493:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181121563:ℝ)/42188800)-4 = (12366363:ℝ)/42188800 by norm_num]
    exact paid_terminal_450
  · change terminalPayment 451 ≤ terminalValue ((point cut hi 1024 451+point cut hi 1024 452)/2)
    have hp : terminalPayment 451 = (462243586599:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 451+point cut hi 1024 452)/2 = (181146713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181146713:ℝ)/42188800) = (2263487:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181146713:ℝ)/42188800)-4 = (12391513:ℝ)/42188800 by norm_num]
    exact paid_terminal_451
  · change terminalPayment 452 ≤ terminalValue ((point cut hi 1024 452+point cut hi 1024 453)/2)
    have hp : terminalPayment 452 = (461668528228:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 452+point cut hi 1024 453)/2 = (181171863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181171863:ℝ)/42188800) = (2262481:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181171863:ℝ)/42188800)-4 = (12416663:ℝ)/42188800 by norm_num]
    exact paid_terminal_452
  · change terminalPayment 453 ≤ terminalValue ((point cut hi 1024 453+point cut hi 1024 454)/2)
    have hp : terminalPayment 453 = (461092833342:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 453+point cut hi 1024 454)/2 = (181197013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181197013:ℝ)/42188800) = (2261475:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181197013:ℝ)/42188800)-4 = (12441813:ℝ)/42188800 by norm_num]
    exact paid_terminal_453
  · change terminalPayment 454 ≤ terminalValue ((point cut hi 1024 454+point cut hi 1024 455)/2)
    have hp : terminalPayment 454 = (460516501225:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 454+point cut hi 1024 455)/2 = (181222163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181222163:ℝ)/42188800) = (2260469:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181222163:ℝ)/42188800)-4 = (12466963:ℝ)/42188800 by norm_num]
    exact paid_terminal_454
  · change terminalPayment 455 ≤ terminalValue ((point cut hi 1024 455+point cut hi 1024 456)/2)
    have hp : terminalPayment 455 = (459939531156:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 455+point cut hi 1024 456)/2 = (181247313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181247313:ℝ)/42188800) = (2259463:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181247313:ℝ)/42188800)-4 = (12492113:ℝ)/42188800 by norm_num]
    exact paid_terminal_455
  · change terminalPayment 456 ≤ terminalValue ((point cut hi 1024 456+point cut hi 1024 457)/2)
    have hp : terminalPayment 456 = (459361922416:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 456+point cut hi 1024 457)/2 = (181272463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181272463:ℝ)/42188800) = (2258457:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181272463:ℝ)/42188800)-4 = (12517263:ℝ)/42188800 by norm_num]
    exact paid_terminal_456
  · change terminalPayment 457 ≤ terminalValue ((point cut hi 1024 457+point cut hi 1024 458)/2)
    have hp : terminalPayment 457 = (458783674284:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 457+point cut hi 1024 458)/2 = (1760171:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((1760171:ℝ)/409600) = (21917:ℝ)/16384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((1760171:ℝ)/409600)-4 = (121771:ℝ)/409600 by norm_num]
    exact paid_terminal_457
  · change terminalPayment 458 ≤ terminalValue ((point cut hi 1024 458+point cut hi 1024 459)/2)
    have hp : terminalPayment 458 = (458204786038:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 458+point cut hi 1024 459)/2 = (181322763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181322763:ℝ)/42188800) = (2256445:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181322763:ℝ)/42188800)-4 = (12567563:ℝ)/42188800 by norm_num]
    exact paid_terminal_458
  · change terminalPayment 459 ≤ terminalValue ((point cut hi 1024 459+point cut hi 1024 460)/2)
    have hp : terminalPayment 459 = (457625256953:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 459+point cut hi 1024 460)/2 = (181347913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181347913:ℝ)/42188800) = (2255439:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181347913:ℝ)/42188800)-4 = (12592713:ℝ)/42188800 by norm_num]
    exact paid_terminal_459
  · change terminalPayment 460 ≤ terminalValue ((point cut hi 1024 460+point cut hi 1024 461)/2)
    have hp : terminalPayment 460 = (457045086306:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 460+point cut hi 1024 461)/2 = (181373063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181373063:ℝ)/42188800) = (2254433:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181373063:ℝ)/42188800)-4 = (12617863:ℝ)/42188800 by norm_num]
    exact paid_terminal_460
  · change terminalPayment 461 ≤ terminalValue ((point cut hi 1024 461+point cut hi 1024 462)/2)
    have hp : terminalPayment 461 = (456464273370:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 461+point cut hi 1024 462)/2 = (181398213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181398213:ℝ)/42188800) = (2253427:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181398213:ℝ)/42188800)-4 = (12643013:ℝ)/42188800 by norm_num]
    exact paid_terminal_461
  · change terminalPayment 462 ≤ terminalValue ((point cut hi 1024 462+point cut hi 1024 463)/2)
    have hp : terminalPayment 462 = (455882817419:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 462+point cut hi 1024 463)/2 = (181423363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181423363:ℝ)/42188800) = (2252421:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181423363:ℝ)/42188800)-4 = (12668163:ℝ)/42188800 by norm_num]
    exact paid_terminal_462
  · change terminalPayment 463 ≤ terminalValue ((point cut hi 1024 463+point cut hi 1024 464)/2)
    have hp : terminalPayment 463 = (455300717723:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 463+point cut hi 1024 464)/2 = (181448513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((181448513:ℝ)/42188800) = (2251415:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((181448513:ℝ)/42188800)-4 = (12693313:ℝ)/42188800 by norm_num]
    exact paid_terminal_463
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_028
