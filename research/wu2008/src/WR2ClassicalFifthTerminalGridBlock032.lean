import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints032
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_032 (j : Fin 16) : terminalPayment (16*32+j.val) ≤
    terminalValue ((point cut hi 1024 (16*32+j.val)+point cut hi 1024 (16*32+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 512 ≤ terminalValue ((point cut hi 1024 512+point cut hi 1024 513)/2)
    have hp : terminalPayment 512 = (425973747226:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 512+point cut hi 1024 513)/2 = (182680863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182680863:ℝ)/42188800) = (2202121:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182680863:ℝ)/42188800)-4 = (13925663:ℝ)/42188800 by norm_num]
    exact paid_terminal_512
  · change terminalPayment 513 ≤ terminalValue ((point cut hi 1024 513+point cut hi 1024 514)/2)
    have hp : terminalPayment 513 = (425358504518:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 513+point cut hi 1024 514)/2 = (182706013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182706013:ℝ)/42188800) = (2201115:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182706013:ℝ)/42188800)-4 = (13950813:ℝ)/42188800 by norm_num]
    exact paid_terminal_513
  · change terminalPayment 514 ≤ terminalValue ((point cut hi 1024 514+point cut hi 1024 515)/2)
    have hp : terminalPayment 514 = (424742579276:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 514+point cut hi 1024 515)/2 = (182731163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182731163:ℝ)/42188800) = (2200109:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182731163:ℝ)/42188800)-4 = (13975963:ℝ)/42188800 by norm_num]
    exact paid_terminal_514
  · change terminalPayment 515 ≤ terminalValue ((point cut hi 1024 515+point cut hi 1024 516)/2)
    have hp : terminalPayment 515 = (424125970707:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 515+point cut hi 1024 516)/2 = (182756313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182756313:ℝ)/42188800) = (2199103:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182756313:ℝ)/42188800)-4 = (14001113:ℝ)/42188800 by norm_num]
    exact paid_terminal_515
  · change terminalPayment 516 ≤ terminalValue ((point cut hi 1024 516+point cut hi 1024 517)/2)
    have hp : terminalPayment 516 = (423508678016:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 516+point cut hi 1024 517)/2 = (182781463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182781463:ℝ)/42188800) = (2198097:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182781463:ℝ)/42188800)-4 = (14026263:ℝ)/42188800 by norm_num]
    exact paid_terminal_516
  · change terminalPayment 517 ≤ terminalValue ((point cut hi 1024 517+point cut hi 1024 518)/2)
    have hp : terminalPayment 517 = (422890700406:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 517+point cut hi 1024 518)/2 = (182806613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182806613:ℝ)/42188800) = (2197091:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182806613:ℝ)/42188800)-4 = (14051413:ℝ)/42188800 by norm_num]
    exact paid_terminal_517
  · change terminalPayment 518 ≤ terminalValue ((point cut hi 1024 518+point cut hi 1024 519)/2)
    have hp : terminalPayment 518 = (422272037079:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 518+point cut hi 1024 519)/2 = (182831763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182831763:ℝ)/42188800) = (2196085:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182831763:ℝ)/42188800)-4 = (14076563:ℝ)/42188800 by norm_num]
    exact paid_terminal_518
  · change terminalPayment 519 ≤ terminalValue ((point cut hi 1024 519+point cut hi 1024 520)/2)
    have hp : terminalPayment 519 = (421652687237:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 519+point cut hi 1024 520)/2 = (182856913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182856913:ℝ)/42188800) = (2195079:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182856913:ℝ)/42188800)-4 = (14101713:ℝ)/42188800 by norm_num]
    exact paid_terminal_519
  · change terminalPayment 520 ≤ terminalValue ((point cut hi 1024 520+point cut hi 1024 521)/2)
    have hp : terminalPayment 520 = (421032650078:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 520+point cut hi 1024 521)/2 = (182882063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182882063:ℝ)/42188800) = (2194073:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182882063:ℝ)/42188800)-4 = (14126863:ℝ)/42188800 by norm_num]
    exact paid_terminal_520
  · change terminalPayment 521 ≤ terminalValue ((point cut hi 1024 521+point cut hi 1024 522)/2)
    have hp : terminalPayment 521 = (420411924802:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 521+point cut hi 1024 522)/2 = (182907213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182907213:ℝ)/42188800) = (2193067:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182907213:ℝ)/42188800)-4 = (14152013:ℝ)/42188800 by norm_num]
    exact paid_terminal_521
  · change terminalPayment 522 ≤ terminalValue ((point cut hi 1024 522+point cut hi 1024 523)/2)
    have hp : terminalPayment 522 = (419790510605:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 522+point cut hi 1024 523)/2 = (182932363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182932363:ℝ)/42188800) = (2192061:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182932363:ℝ)/42188800)-4 = (14177163:ℝ)/42188800 by norm_num]
    exact paid_terminal_522
  · change terminalPayment 523 ≤ terminalValue ((point cut hi 1024 523+point cut hi 1024 524)/2)
    have hp : terminalPayment 523 = (419168406682:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 523+point cut hi 1024 524)/2 = (182957513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182957513:ℝ)/42188800) = (2191055:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182957513:ℝ)/42188800)-4 = (14202313:ℝ)/42188800 by norm_num]
    exact paid_terminal_523
  · change terminalPayment 524 ≤ terminalValue ((point cut hi 1024 524+point cut hi 1024 525)/2)
    have hp : terminalPayment 524 = (418545612228:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 524+point cut hi 1024 525)/2 = (182982663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182982663:ℝ)/42188800) = (2190049:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182982663:ℝ)/42188800)-4 = (14227463:ℝ)/42188800 by norm_num]
    exact paid_terminal_524
  · change terminalPayment 525 ≤ terminalValue ((point cut hi 1024 525+point cut hi 1024 526)/2)
    have hp : terminalPayment 525 = (417922126435:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 525+point cut hi 1024 526)/2 = (183007813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183007813:ℝ)/42188800) = (2189043:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183007813:ℝ)/42188800)-4 = (14252613:ℝ)/42188800 by norm_num]
    exact paid_terminal_525
  · change terminalPayment 526 ≤ terminalValue ((point cut hi 1024 526+point cut hi 1024 527)/2)
    have hp : terminalPayment 526 = (417297948495:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 526+point cut hi 1024 527)/2 = (183032963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183032963:ℝ)/42188800) = (2188037:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183032963:ℝ)/42188800)-4 = (14277763:ℝ)/42188800 by norm_num]
    exact paid_terminal_526
  · change terminalPayment 527 ≤ terminalValue ((point cut hi 1024 527+point cut hi 1024 528)/2)
    have hp : terminalPayment 527 = (416673077598:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 527+point cut hi 1024 528)/2 = (183058113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183058113:ℝ)/42188800) = (2187031:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183058113:ℝ)/42188800)-4 = (14302913:ℝ)/42188800 by norm_num]
    exact paid_terminal_527
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_032
