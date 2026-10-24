import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints006
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_006 (j : Fin 16) : terminalPayment (16*6+j.val) ≤
    terminalValue ((point cut hi 1024 (16*6+j.val)+point cut hi 1024 (16*6+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 96 ≤ terminalValue ((point cut hi 1024 96+point cut hi 1024 97)/2)
    have hp : terminalPayment 96 = (630851714912:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 96+point cut hi 1024 97)/2 = (172218463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172218463:ℝ)/42188800) = (2620617:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172218463:ℝ)/42188800)-4 = (3463263:ℝ)/42188800 by norm_num]
    exact paid_terminal_96
  · change terminalPayment 97 ≤ terminalValue ((point cut hi 1024 97+point cut hi 1024 98)/2)
    have hp : terminalPayment 97 = (630465025182:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 97+point cut hi 1024 98)/2 = (172243613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172243613:ℝ)/42188800) = (2619611:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172243613:ℝ)/42188800)-4 = (3488413:ℝ)/42188800 by norm_num]
    exact paid_terminal_97
  · change terminalPayment 98 ≤ terminalValue ((point cut hi 1024 98+point cut hi 1024 99)/2)
    have hp : terminalPayment 98 = (630077891305:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 98+point cut hi 1024 99)/2 = (172268763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172268763:ℝ)/42188800) = (2618605:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172268763:ℝ)/42188800)-4 = (3513563:ℝ)/42188800 by norm_num]
    exact paid_terminal_98
  · change terminalPayment 99 ≤ terminalValue ((point cut hi 1024 99+point cut hi 1024 100)/2)
    have hp : terminalPayment 99 = (629690312886:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 99+point cut hi 1024 100)/2 = (172293913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172293913:ℝ)/42188800) = (2617599:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172293913:ℝ)/42188800)-4 = (3538713:ℝ)/42188800 by norm_num]
    exact paid_terminal_99
  · change terminalPayment 100 ≤ terminalValue ((point cut hi 1024 100+point cut hi 1024 101)/2)
    have hp : terminalPayment 100 = (629302289527:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 100+point cut hi 1024 101)/2 = (172319063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172319063:ℝ)/42188800) = (2616593:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172319063:ℝ)/42188800)-4 = (3563863:ℝ)/42188800 by norm_num]
    exact paid_terminal_100
  · change terminalPayment 101 ≤ terminalValue ((point cut hi 1024 101+point cut hi 1024 102)/2)
    have hp : terminalPayment 101 = (628913820832:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 101+point cut hi 1024 102)/2 = (172344213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172344213:ℝ)/42188800) = (2615587:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172344213:ℝ)/42188800)-4 = (3589013:ℝ)/42188800 by norm_num]
    exact paid_terminal_101
  · change terminalPayment 102 ≤ terminalValue ((point cut hi 1024 102+point cut hi 1024 103)/2)
    have hp : terminalPayment 102 = (628524906403:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 102+point cut hi 1024 103)/2 = (172369363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172369363:ℝ)/42188800) = (2614581:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172369363:ℝ)/42188800)-4 = (3614163:ℝ)/42188800 by norm_num]
    exact paid_terminal_102
  · change terminalPayment 103 ≤ terminalValue ((point cut hi 1024 103+point cut hi 1024 104)/2)
    have hp : terminalPayment 103 = (628135545841:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 103+point cut hi 1024 104)/2 = (172394513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172394513:ℝ)/42188800) = (2613575:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172394513:ℝ)/42188800)-4 = (3639313:ℝ)/42188800 by norm_num]
    exact paid_terminal_103
  · change terminalPayment 104 ≤ terminalValue ((point cut hi 1024 104+point cut hi 1024 105)/2)
    have hp : terminalPayment 104 = (627745738748:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 104+point cut hi 1024 105)/2 = (172419663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172419663:ℝ)/42188800) = (2612569:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172419663:ℝ)/42188800)-4 = (3664463:ℝ)/42188800 by norm_num]
    exact paid_terminal_104
  · change terminalPayment 105 ≤ terminalValue ((point cut hi 1024 105+point cut hi 1024 106)/2)
    have hp : terminalPayment 105 = (627355484724:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 105+point cut hi 1024 106)/2 = (172444813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172444813:ℝ)/42188800) = (2611563:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172444813:ℝ)/42188800)-4 = (3689613:ℝ)/42188800 by norm_num]
    exact paid_terminal_105
  · change terminalPayment 106 ≤ terminalValue ((point cut hi 1024 106+point cut hi 1024 107)/2)
    have hp : terminalPayment 106 = (626964783368:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 106+point cut hi 1024 107)/2 = (172469963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172469963:ℝ)/42188800) = (2610557:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172469963:ℝ)/42188800)-4 = (3714763:ℝ)/42188800 by norm_num]
    exact paid_terminal_106
  · change terminalPayment 107 ≤ terminalValue ((point cut hi 1024 107+point cut hi 1024 108)/2)
    have hp : terminalPayment 107 = (626573634278:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 107+point cut hi 1024 108)/2 = (172495113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172495113:ℝ)/42188800) = (2609551:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172495113:ℝ)/42188800)-4 = (3739913:ℝ)/42188800 by norm_num]
    exact paid_terminal_107
  · change terminalPayment 108 ≤ terminalValue ((point cut hi 1024 108+point cut hi 1024 109)/2)
    have hp : terminalPayment 108 = (626182037053:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 108+point cut hi 1024 109)/2 = (172520263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172520263:ℝ)/42188800) = (2608545:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172520263:ℝ)/42188800)-4 = (3765063:ℝ)/42188800 by norm_num]
    exact paid_terminal_108
  · change terminalPayment 109 ≤ terminalValue ((point cut hi 1024 109+point cut hi 1024 110)/2)
    have hp : terminalPayment 109 = (625789991289:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 109+point cut hi 1024 110)/2 = (172545413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172545413:ℝ)/42188800) = (2607539:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172545413:ℝ)/42188800)-4 = (3790213:ℝ)/42188800 by norm_num]
    exact paid_terminal_109
  · change terminalPayment 110 ≤ terminalValue ((point cut hi 1024 110+point cut hi 1024 111)/2)
    have hp : terminalPayment 110 = (625397496585:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 110+point cut hi 1024 111)/2 = (172570563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172570563:ℝ)/42188800) = (2606533:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172570563:ℝ)/42188800)-4 = (3815363:ℝ)/42188800 by norm_num]
    exact paid_terminal_110
  · change terminalPayment 111 ≤ terminalValue ((point cut hi 1024 111+point cut hi 1024 112)/2)
    have hp : terminalPayment 111 = (625004552535:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 111+point cut hi 1024 112)/2 = (172595713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172595713:ℝ)/42188800) = (2605527:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172595713:ℝ)/42188800)-4 = (3840513:ℝ)/42188800 by norm_num]
    exact paid_terminal_111
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_006
