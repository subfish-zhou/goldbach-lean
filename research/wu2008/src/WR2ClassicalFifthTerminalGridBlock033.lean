import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints033
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_033 (j : Fin 16) : terminalPayment (16*33+j.val) ≤
    terminalValue ((point cut hi 1024 (16*33+j.val)+point cut hi 1024 (16*33+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 528 ≤ terminalValue ((point cut hi 1024 528+point cut hi 1024 529)/2)
    have hp : terminalPayment 528 = (416047512934:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 528+point cut hi 1024 529)/2 = (183083263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183083263:ℝ)/42188800) = (2186025:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183083263:ℝ)/42188800)-4 = (14328063:ℝ)/42188800 by norm_num]
    exact paid_terminal_528
  · change terminalPayment 529 ≤ terminalValue ((point cut hi 1024 529+point cut hi 1024 530)/2)
    have hp : terminalPayment 529 = (415421253689:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 529+point cut hi 1024 530)/2 = (183108413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183108413:ℝ)/42188800) = (2185019:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183108413:ℝ)/42188800)-4 = (14353213:ℝ)/42188800 by norm_num]
    exact paid_terminal_529
  · change terminalPayment 530 ≤ terminalValue ((point cut hi 1024 530+point cut hi 1024 531)/2)
    have hp : terminalPayment 530 = (414794299049:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 530+point cut hi 1024 531)/2 = (183133563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183133563:ℝ)/42188800) = (2184013:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183133563:ℝ)/42188800)-4 = (14378363:ℝ)/42188800 by norm_num]
    exact paid_terminal_530
  · change terminalPayment 531 ≤ terminalValue ((point cut hi 1024 531+point cut hi 1024 532)/2)
    have hp : terminalPayment 531 = (414166648200:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 531+point cut hi 1024 532)/2 = (183158713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183158713:ℝ)/42188800) = (2183007:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183158713:ℝ)/42188800)-4 = (14403513:ℝ)/42188800 by norm_num]
    exact paid_terminal_531
  · change terminalPayment 532 ≤ terminalValue ((point cut hi 1024 532+point cut hi 1024 533)/2)
    have hp : terminalPayment 532 = (413538300325:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 532+point cut hi 1024 533)/2 = (183183863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183183863:ℝ)/42188800) = (2182001:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183183863:ℝ)/42188800)-4 = (14428663:ℝ)/42188800 by norm_num]
    exact paid_terminal_532
  · change terminalPayment 533 ≤ terminalValue ((point cut hi 1024 533+point cut hi 1024 534)/2)
    have hp : terminalPayment 533 = (412909254605:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 533+point cut hi 1024 534)/2 = (183209013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183209013:ℝ)/42188800) = (2180995:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183209013:ℝ)/42188800)-4 = (14453813:ℝ)/42188800 by norm_num]
    exact paid_terminal_533
  · change terminalPayment 534 ≤ terminalValue ((point cut hi 1024 534+point cut hi 1024 535)/2)
    have hp : terminalPayment 534 = (412279510222:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 534+point cut hi 1024 535)/2 = (183234163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183234163:ℝ)/42188800) = (2179989:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183234163:ℝ)/42188800)-4 = (14478963:ℝ)/42188800 by norm_num]
    exact paid_terminal_534
  · change terminalPayment 535 ≤ terminalValue ((point cut hi 1024 535+point cut hi 1024 536)/2)
    have hp : terminalPayment 535 = (411649066354:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 535+point cut hi 1024 536)/2 = (183259313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183259313:ℝ)/42188800) = (2178983:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183259313:ℝ)/42188800)-4 = (14504113:ℝ)/42188800 by norm_num]
    exact paid_terminal_535
  · change terminalPayment 536 ≤ terminalValue ((point cut hi 1024 536+point cut hi 1024 537)/2)
    have hp : terminalPayment 536 = (411017922180:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 536+point cut hi 1024 537)/2 = (183284463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183284463:ℝ)/42188800) = (2177977:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183284463:ℝ)/42188800)-4 = (14529263:ℝ)/42188800 by norm_num]
    exact paid_terminal_536
  · change terminalPayment 537 ≤ terminalValue ((point cut hi 1024 537+point cut hi 1024 538)/2)
    have hp : terminalPayment 537 = (410386076876:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 537+point cut hi 1024 538)/2 = (183309613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183309613:ℝ)/42188800) = (2176971:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183309613:ℝ)/42188800)-4 = (14554413:ℝ)/42188800 by norm_num]
    exact paid_terminal_537
  · change terminalPayment 538 ≤ terminalValue ((point cut hi 1024 538+point cut hi 1024 539)/2)
    have hp : terminalPayment 538 = (409753529618:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 538+point cut hi 1024 539)/2 = (183334763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183334763:ℝ)/42188800) = (2175965:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183334763:ℝ)/42188800)-4 = (14579563:ℝ)/42188800 by norm_num]
    exact paid_terminal_538
  · change terminalPayment 539 ≤ terminalValue ((point cut hi 1024 539+point cut hi 1024 540)/2)
    have hp : terminalPayment 539 = (409120279579:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 539+point cut hi 1024 540)/2 = (183359913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183359913:ℝ)/42188800) = (2174959:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183359913:ℝ)/42188800)-4 = (14604713:ℝ)/42188800 by norm_num]
    exact paid_terminal_539
  · change terminalPayment 540 ≤ terminalValue ((point cut hi 1024 540+point cut hi 1024 541)/2)
    have hp : terminalPayment 540 = (408486325932:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 540+point cut hi 1024 541)/2 = (183385063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183385063:ℝ)/42188800) = (2173953:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183385063:ℝ)/42188800)-4 = (14629863:ℝ)/42188800 by norm_num]
    exact paid_terminal_540
  · change terminalPayment 541 ≤ terminalValue ((point cut hi 1024 541+point cut hi 1024 542)/2)
    have hp : terminalPayment 541 = (407851667848:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 541+point cut hi 1024 542)/2 = (183410213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183410213:ℝ)/42188800) = (2172947:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183410213:ℝ)/42188800)-4 = (14655013:ℝ)/42188800 by norm_num]
    exact paid_terminal_541
  · change terminalPayment 542 ≤ terminalValue ((point cut hi 1024 542+point cut hi 1024 543)/2)
    have hp : terminalPayment 542 = (407216304496:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 542+point cut hi 1024 543)/2 = (183435363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183435363:ℝ)/42188800) = (2171941:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183435363:ℝ)/42188800)-4 = (14680163:ℝ)/42188800 by norm_num]
    exact paid_terminal_542
  · change terminalPayment 543 ≤ terminalValue ((point cut hi 1024 543+point cut hi 1024 544)/2)
    have hp : terminalPayment 543 = (406580235044:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 543+point cut hi 1024 544)/2 = (183460513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((183460513:ℝ)/42188800) = (2170935:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((183460513:ℝ)/42188800)-4 = (14705313:ℝ)/42188800 by norm_num]
    exact paid_terminal_543
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_033
