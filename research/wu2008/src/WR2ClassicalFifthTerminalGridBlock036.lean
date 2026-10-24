import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints036
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_036 (j : Fin 16) : terminalPayment (16*36+j.val) ≤
    terminalValue ((point cut hi 1024 (16*36+j.val)+point cut hi 1024 (16*36+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 576 ≤ terminalValue ((point cut hi 1024 576+point cut hi 1024 577)/2)
    have hp : terminalPayment 576 = (385188295209:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 576+point cut hi 1024 577)/2 = (184290463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184290463:ℝ)/42188800) = (2137737:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184290463:ℝ)/42188800)-4 = (15535263:ℝ)/42188800 by norm_num]
    exact paid_terminal_576
  · change terminalPayment 577 ≤ terminalValue ((point cut hi 1024 577+point cut hi 1024 578)/2)
    have hp : terminalPayment 577 = (384527713454:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 577+point cut hi 1024 578)/2 = (184315613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184315613:ℝ)/42188800) = (2136731:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184315613:ℝ)/42188800)-4 = (15560413:ℝ)/42188800 by norm_num]
    exact paid_terminal_577
  · change terminalPayment 578 ≤ terminalValue ((point cut hi 1024 578+point cut hi 1024 579)/2)
    have hp : terminalPayment 578 = (383866395598:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 578+point cut hi 1024 579)/2 = (184340763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184340763:ℝ)/42188800) = (2135725:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184340763:ℝ)/42188800)-4 = (15585563:ℝ)/42188800 by norm_num]
    exact paid_terminal_578
  · change terminalPayment 579 ≤ terminalValue ((point cut hi 1024 579+point cut hi 1024 580)/2)
    have hp : terminalPayment 579 = (383204340757:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 579+point cut hi 1024 580)/2 = (184365913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184365913:ℝ)/42188800) = (2134719:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184365913:ℝ)/42188800)-4 = (15610713:ℝ)/42188800 by norm_num]
    exact paid_terminal_579
  · change terminalPayment 580 ≤ terminalValue ((point cut hi 1024 580+point cut hi 1024 581)/2)
    have hp : terminalPayment 580 = (382541548045:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 580+point cut hi 1024 581)/2 = (184391063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184391063:ℝ)/42188800) = (2133713:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184391063:ℝ)/42188800)-4 = (15635863:ℝ)/42188800 by norm_num]
    exact paid_terminal_580
  · change terminalPayment 581 ≤ terminalValue ((point cut hi 1024 581+point cut hi 1024 582)/2)
    have hp : terminalPayment 581 = (381878016577:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 581+point cut hi 1024 582)/2 = (184416213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184416213:ℝ)/42188800) = (2132707:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184416213:ℝ)/42188800)-4 = (15661013:ℝ)/42188800 by norm_num]
    exact paid_terminal_581
  · change terminalPayment 582 ≤ terminalValue ((point cut hi 1024 582+point cut hi 1024 583)/2)
    have hp : terminalPayment 582 = (381213745466:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 582+point cut hi 1024 583)/2 = (184441363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184441363:ℝ)/42188800) = (2131701:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184441363:ℝ)/42188800)-4 = (15686163:ℝ)/42188800 by norm_num]
    exact paid_terminal_582
  · change terminalPayment 583 ≤ terminalValue ((point cut hi 1024 583+point cut hi 1024 584)/2)
    have hp : terminalPayment 583 = (380548733821:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 583+point cut hi 1024 584)/2 = (184466513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184466513:ℝ)/42188800) = (2130695:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184466513:ℝ)/42188800)-4 = (15711313:ℝ)/42188800 by norm_num]
    exact paid_terminal_583
  · change terminalPayment 584 ≤ terminalValue ((point cut hi 1024 584+point cut hi 1024 585)/2)
    have hp : terminalPayment 584 = (379882980751:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 584+point cut hi 1024 585)/2 = (184491663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184491663:ℝ)/42188800) = (2129689:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184491663:ℝ)/42188800)-4 = (15736463:ℝ)/42188800 by norm_num]
    exact paid_terminal_584
  · change terminalPayment 585 ≤ terminalValue ((point cut hi 1024 585+point cut hi 1024 586)/2)
    have hp : terminalPayment 585 = (379216485366:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 585+point cut hi 1024 586)/2 = (184516813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184516813:ℝ)/42188800) = (2128683:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184516813:ℝ)/42188800)-4 = (15761613:ℝ)/42188800 by norm_num]
    exact paid_terminal_585
  · change terminalPayment 586 ≤ terminalValue ((point cut hi 1024 586+point cut hi 1024 587)/2)
    have hp : terminalPayment 586 = (378549246770:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 586+point cut hi 1024 587)/2 = (184541963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184541963:ℝ)/42188800) = (2127677:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184541963:ℝ)/42188800)-4 = (15786763:ℝ)/42188800 by norm_num]
    exact paid_terminal_586
  · change terminalPayment 587 ≤ terminalValue ((point cut hi 1024 587+point cut hi 1024 588)/2)
    have hp : terminalPayment 587 = (377881264069:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 587+point cut hi 1024 588)/2 = (184567113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184567113:ℝ)/42188800) = (2126671:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184567113:ℝ)/42188800)-4 = (15811913:ℝ)/42188800 by norm_num]
    exact paid_terminal_587
  · change terminalPayment 588 ≤ terminalValue ((point cut hi 1024 588+point cut hi 1024 589)/2)
    have hp : terminalPayment 588 = (377212536366:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 588+point cut hi 1024 589)/2 = (184592263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184592263:ℝ)/42188800) = (2125665:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184592263:ℝ)/42188800)-4 = (15837063:ℝ)/42188800 by norm_num]
    exact paid_terminal_588
  · change terminalPayment 589 ≤ terminalValue ((point cut hi 1024 589+point cut hi 1024 590)/2)
    have hp : terminalPayment 589 = (376543062762:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 589+point cut hi 1024 590)/2 = (184617413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184617413:ℝ)/42188800) = (2124659:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184617413:ℝ)/42188800)-4 = (15862213:ℝ)/42188800 by norm_num]
    exact paid_terminal_589
  · change terminalPayment 590 ≤ terminalValue ((point cut hi 1024 590+point cut hi 1024 591)/2)
    have hp : terminalPayment 590 = (375872842359:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 590+point cut hi 1024 591)/2 = (184642563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184642563:ℝ)/42188800) = (2123653:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184642563:ℝ)/42188800)-4 = (15887363:ℝ)/42188800 by norm_num]
    exact paid_terminal_590
  · change terminalPayment 591 ≤ terminalValue ((point cut hi 1024 591+point cut hi 1024 592)/2)
    have hp : terminalPayment 591 = (375201874254:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 591+point cut hi 1024 592)/2 = (184667713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((184667713:ℝ)/42188800) = (2122647:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((184667713:ℝ)/42188800)-4 = (15912513:ℝ)/42188800 by norm_num]
    exact paid_terminal_591
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_036
