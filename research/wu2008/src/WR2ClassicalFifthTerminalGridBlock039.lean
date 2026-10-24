import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints039
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_039 (j : Fin 16) : terminalPayment (16*39+j.val) ≤
    terminalValue ((point cut hi 1024 (16*39+j.val)+point cut hi 1024 (16*39+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 624 ≤ terminalValue ((point cut hi 1024 624+point cut hi 1024 625)/2)
    have hp : terminalPayment 624 = (352634476951:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 624+point cut hi 1024 625)/2 = (185497663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185497663:ℝ)/42188800) = (2089449:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185497663:ℝ)/42188800)-4 = (16742463:ℝ)/42188800 by norm_num]
    exact paid_terminal_624
  · change terminalPayment 625 ≤ terminalValue ((point cut hi 1024 625+point cut hi 1024 626)/2)
    have hp : terminalPayment 625 = (351937539735:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 625+point cut hi 1024 626)/2 = (185522813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185522813:ℝ)/42188800) = (2088443:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185522813:ℝ)/42188800)-4 = (16767613:ℝ)/42188800 by norm_num]
    exact paid_terminal_625
  · change terminalPayment 626 ≤ terminalValue ((point cut hi 1024 626+point cut hi 1024 627)/2)
    have hp : terminalPayment 626 = (351239822296:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 626+point cut hi 1024 627)/2 = (185547963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185547963:ℝ)/42188800) = (2087437:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185547963:ℝ)/42188800)-4 = (16792763:ℝ)/42188800 by norm_num]
    exact paid_terminal_626
  · change terminalPayment 627 ≤ terminalValue ((point cut hi 1024 627+point cut hi 1024 628)/2)
    have hp : terminalPayment 627 = (350541323677:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 627+point cut hi 1024 628)/2 = (185573113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185573113:ℝ)/42188800) = (2086431:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185573113:ℝ)/42188800)-4 = (16817913:ℝ)/42188800 by norm_num]
    exact paid_terminal_627
  · change terminalPayment 628 ≤ terminalValue ((point cut hi 1024 628+point cut hi 1024 629)/2)
    have hp : terminalPayment 628 = (349842042919:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 628+point cut hi 1024 629)/2 = (185598263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185598263:ℝ)/42188800) = (2085425:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185598263:ℝ)/42188800)-4 = (16843063:ℝ)/42188800 by norm_num]
    exact paid_terminal_628
  · change terminalPayment 629 ≤ terminalValue ((point cut hi 1024 629+point cut hi 1024 630)/2)
    have hp : terminalPayment 629 = (349141979060:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 629+point cut hi 1024 630)/2 = (185623413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185623413:ℝ)/42188800) = (2084419:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185623413:ℝ)/42188800)-4 = (16868213:ℝ)/42188800 by norm_num]
    exact paid_terminal_629
  · change terminalPayment 630 ≤ terminalValue ((point cut hi 1024 630+point cut hi 1024 631)/2)
    have hp : terminalPayment 630 = (348441131138:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 630+point cut hi 1024 631)/2 = (185648563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185648563:ℝ)/42188800) = (2083413:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185648563:ℝ)/42188800)-4 = (16893363:ℝ)/42188800 by norm_num]
    exact paid_terminal_630
  · change terminalPayment 631 ≤ terminalValue ((point cut hi 1024 631+point cut hi 1024 632)/2)
    have hp : terminalPayment 631 = (347739498188:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 631+point cut hi 1024 632)/2 = (185673713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185673713:ℝ)/42188800) = (2082407:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185673713:ℝ)/42188800)-4 = (16918513:ℝ)/42188800 by norm_num]
    exact paid_terminal_631
  · change terminalPayment 632 ≤ terminalValue ((point cut hi 1024 632+point cut hi 1024 633)/2)
    have hp : terminalPayment 632 = (347037079246:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 632+point cut hi 1024 633)/2 = (185698863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185698863:ℝ)/42188800) = (2081401:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185698863:ℝ)/42188800)-4 = (16943663:ℝ)/42188800 by norm_num]
    exact paid_terminal_632
  · change terminalPayment 633 ≤ terminalValue ((point cut hi 1024 633+point cut hi 1024 634)/2)
    have hp : terminalPayment 633 = (346333873343:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 633+point cut hi 1024 634)/2 = (185724013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185724013:ℝ)/42188800) = (2080395:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185724013:ℝ)/42188800)-4 = (16968813:ℝ)/42188800 by norm_num]
    exact paid_terminal_633
  · change terminalPayment 634 ≤ terminalValue ((point cut hi 1024 634+point cut hi 1024 635)/2)
    have hp : terminalPayment 634 = (345629879511:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 634+point cut hi 1024 635)/2 = (185749163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185749163:ℝ)/42188800) = (2079389:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185749163:ℝ)/42188800)-4 = (16993963:ℝ)/42188800 by norm_num]
    exact paid_terminal_634
  · change terminalPayment 635 ≤ terminalValue ((point cut hi 1024 635+point cut hi 1024 636)/2)
    have hp : terminalPayment 635 = (344925096778:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 635+point cut hi 1024 636)/2 = (185774313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185774313:ℝ)/42188800) = (2078383:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185774313:ℝ)/42188800)-4 = (17019113:ℝ)/42188800 by norm_num]
    exact paid_terminal_635
  · change terminalPayment 636 ≤ terminalValue ((point cut hi 1024 636+point cut hi 1024 637)/2)
    have hp : terminalPayment 636 = (344219524172:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 636+point cut hi 1024 637)/2 = (185799463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185799463:ℝ)/42188800) = (2077377:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185799463:ℝ)/42188800)-4 = (17044263:ℝ)/42188800 by norm_num]
    exact paid_terminal_636
  · change terminalPayment 637 ≤ terminalValue ((point cut hi 1024 637+point cut hi 1024 638)/2)
    have hp : terminalPayment 637 = (343513160719:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 637+point cut hi 1024 638)/2 = (185824613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185824613:ℝ)/42188800) = (2076371:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185824613:ℝ)/42188800)-4 = (17069413:ℝ)/42188800 by norm_num]
    exact paid_terminal_637
  · change terminalPayment 638 ≤ terminalValue ((point cut hi 1024 638+point cut hi 1024 639)/2)
    have hp : terminalPayment 638 = (342806005443:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 638+point cut hi 1024 639)/2 = (185849763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185849763:ℝ)/42188800) = (2075365:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185849763:ℝ)/42188800)-4 = (17094563:ℝ)/42188800 by norm_num]
    exact paid_terminal_638
  · change terminalPayment 639 ≤ terminalValue ((point cut hi 1024 639+point cut hi 1024 640)/2)
    have hp : terminalPayment 639 = (342098057367:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 639+point cut hi 1024 640)/2 = (185874913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185874913:ℝ)/42188800) = (2074359:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185874913:ℝ)/42188800)-4 = (17119713:ℝ)/42188800 by norm_num]
    exact paid_terminal_639
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_039
