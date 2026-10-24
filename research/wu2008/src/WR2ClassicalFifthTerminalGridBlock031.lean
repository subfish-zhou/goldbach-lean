import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints031
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_031 (j : Fin 16) : terminalPayment (16*31+j.val) ≤
    terminalValue ((point cut hi 1024 (16*31+j.val)+point cut hi 1024 (16*31+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 496 ≤ terminalValue ((point cut hi 1024 496+point cut hi 1024 497)/2)
    have hp : terminalPayment 496 = (435725448734:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 496+point cut hi 1024 497)/2 = (182278463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182278463:ℝ)/42188800) = (2218217:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182278463:ℝ)/42188800)-4 = (13523263:ℝ)/42188800 by norm_num]
    exact paid_terminal_496
  · change terminalPayment 497 ≤ terminalValue ((point cut hi 1024 497+point cut hi 1024 498)/2)
    have hp : terminalPayment 497 = (435121019663:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 497+point cut hi 1024 498)/2 = (182303613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182303613:ℝ)/42188800) = (2217211:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182303613:ℝ)/42188800)-4 = (13548413:ℝ)/42188800 by norm_num]
    exact paid_terminal_497
  · change terminalPayment 498 ≤ terminalValue ((point cut hi 1024 498+point cut hi 1024 499)/2)
    have hp : terminalPayment 498 = (434515920583:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 498+point cut hi 1024 499)/2 = (182328763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182328763:ℝ)/42188800) = (2216205:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182328763:ℝ)/42188800)-4 = (13573563:ℝ)/42188800 by norm_num]
    exact paid_terminal_498
  · change terminalPayment 499 ≤ terminalValue ((point cut hi 1024 499+point cut hi 1024 500)/2)
    have hp : terminalPayment 499 = (433910150721:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 499+point cut hi 1024 500)/2 = (182353913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182353913:ℝ)/42188800) = (2215199:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182353913:ℝ)/42188800)-4 = (13598713:ℝ)/42188800 by norm_num]
    exact paid_terminal_499
  · change terminalPayment 500 ≤ terminalValue ((point cut hi 1024 500+point cut hi 1024 501)/2)
    have hp : terminalPayment 500 = (433303709301:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 500+point cut hi 1024 501)/2 = (182379063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182379063:ℝ)/42188800) = (2214193:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182379063:ℝ)/42188800)-4 = (13623863:ℝ)/42188800 by norm_num]
    exact paid_terminal_500
  · change terminalPayment 501 ≤ terminalValue ((point cut hi 1024 501+point cut hi 1024 502)/2)
    have hp : terminalPayment 501 = (432696595549:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 501+point cut hi 1024 502)/2 = (182404213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182404213:ℝ)/42188800) = (2213187:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182404213:ℝ)/42188800)-4 = (13649013:ℝ)/42188800 by norm_num]
    exact paid_terminal_501
  · change terminalPayment 502 ≤ terminalValue ((point cut hi 1024 502+point cut hi 1024 503)/2)
    have hp : terminalPayment 502 = (432088808688:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 502+point cut hi 1024 503)/2 = (182429363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182429363:ℝ)/42188800) = (2212181:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182429363:ℝ)/42188800)-4 = (13674163:ℝ)/42188800 by norm_num]
    exact paid_terminal_502
  · change terminalPayment 503 ≤ terminalValue ((point cut hi 1024 503+point cut hi 1024 504)/2)
    have hp : terminalPayment 503 = (431480347940:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 503+point cut hi 1024 504)/2 = (182454513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182454513:ℝ)/42188800) = (2211175:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182454513:ℝ)/42188800)-4 = (13699313:ℝ)/42188800 by norm_num]
    exact paid_terminal_503
  · change terminalPayment 504 ≤ terminalValue ((point cut hi 1024 504+point cut hi 1024 505)/2)
    have hp : terminalPayment 504 = (430871212525:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 504+point cut hi 1024 505)/2 = (182479663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182479663:ℝ)/42188800) = (2210169:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182479663:ℝ)/42188800)-4 = (13724463:ℝ)/42188800 by norm_num]
    exact paid_terminal_504
  · change terminalPayment 505 ≤ terminalValue ((point cut hi 1024 505+point cut hi 1024 506)/2)
    have hp : terminalPayment 505 = (430261401661:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 505+point cut hi 1024 506)/2 = (182504813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182504813:ℝ)/42188800) = (2209163:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182504813:ℝ)/42188800)-4 = (13749613:ℝ)/42188800 by norm_num]
    exact paid_terminal_505
  · change terminalPayment 506 ≤ terminalValue ((point cut hi 1024 506+point cut hi 1024 507)/2)
    have hp : terminalPayment 506 = (429650914569:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 506+point cut hi 1024 507)/2 = (182529963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182529963:ℝ)/42188800) = (2208157:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182529963:ℝ)/42188800)-4 = (13774763:ℝ)/42188800 by norm_num]
    exact paid_terminal_506
  · change terminalPayment 507 ≤ terminalValue ((point cut hi 1024 507+point cut hi 1024 508)/2)
    have hp : terminalPayment 507 = (429039750463:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 507+point cut hi 1024 508)/2 = (182555113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182555113:ℝ)/42188800) = (2207151:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182555113:ℝ)/42188800)-4 = (13799913:ℝ)/42188800 by norm_num]
    exact paid_terminal_507
  · change terminalPayment 508 ≤ terminalValue ((point cut hi 1024 508+point cut hi 1024 509)/2)
    have hp : terminalPayment 508 = (428427908559:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 508+point cut hi 1024 509)/2 = (182580263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182580263:ℝ)/42188800) = (2206145:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182580263:ℝ)/42188800)-4 = (13825063:ℝ)/42188800 by norm_num]
    exact paid_terminal_508
  · change terminalPayment 509 ≤ terminalValue ((point cut hi 1024 509+point cut hi 1024 510)/2)
    have hp : terminalPayment 509 = (427815388071:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 509+point cut hi 1024 510)/2 = (182605413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182605413:ℝ)/42188800) = (2205139:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182605413:ℝ)/42188800)-4 = (13850213:ℝ)/42188800 by norm_num]
    exact paid_terminal_509
  · change terminalPayment 510 ≤ terminalValue ((point cut hi 1024 510+point cut hi 1024 511)/2)
    have hp : terminalPayment 510 = (427202188212:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 510+point cut hi 1024 511)/2 = (182630563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182630563:ℝ)/42188800) = (2204133:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182630563:ℝ)/42188800)-4 = (13875363:ℝ)/42188800 by norm_num]
    exact paid_terminal_510
  · change terminalPayment 511 ≤ terminalValue ((point cut hi 1024 511+point cut hi 1024 512)/2)
    have hp : terminalPayment 511 = (426588308194:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 511+point cut hi 1024 512)/2 = (182655713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((182655713:ℝ)/42188800) = (2203127:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((182655713:ℝ)/42188800)-4 = (13900513:ℝ)/42188800 by norm_num]
    exact paid_terminal_511
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_031
