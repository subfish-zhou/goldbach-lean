import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints043
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_043 (j : Fin 16) : terminalPayment (16*43+j.val) ≤
    terminalValue ((point cut hi 1024 (16*43+j.val)+point cut hi 1024 (16*43+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 688 ≤ terminalValue ((point cut hi 1024 688+point cut hi 1024 689)/2)
    have hp : terminalPayment 688 = (306416609486:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 688+point cut hi 1024 689)/2 = (187107263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187107263:ℝ)/42188800) = (2025065:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187107263:ℝ)/42188800)-4 = (18352063:ℝ)/42188800 by norm_num]
    exact paid_terminal_688
  · change terminalPayment 689 ≤ terminalValue ((point cut hi 1024 689+point cut hi 1024 690)/2)
    have hp : terminalPayment 689 = (305667737660:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 689+point cut hi 1024 690)/2 = (187132413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187132413:ℝ)/42188800) = (2024059:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187132413:ℝ)/42188800)-4 = (18377213:ℝ)/42188800 by norm_num]
    exact paid_terminal_689
  · change terminalPayment 690 ≤ terminalValue ((point cut hi 1024 690+point cut hi 1024 691)/2)
    have hp : terminalPayment 690 = (304918020913:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 690+point cut hi 1024 691)/2 = (187157563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187157563:ℝ)/42188800) = (2023053:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187157563:ℝ)/42188800)-4 = (18402363:ℝ)/42188800 by norm_num]
    exact paid_terminal_690
  · change terminalPayment 691 ≤ terminalValue ((point cut hi 1024 691+point cut hi 1024 692)/2)
    have hp : terminalPayment 691 = (304167458177:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 691+point cut hi 1024 692)/2 = (187182713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187182713:ℝ)/42188800) = (2022047:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187182713:ℝ)/42188800)-4 = (18427513:ℝ)/42188800 by norm_num]
    exact paid_terminal_691
  · change terminalPayment 692 ≤ terminalValue ((point cut hi 1024 692+point cut hi 1024 693)/2)
    have hp : terminalPayment 692 = (303416048382:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 692+point cut hi 1024 693)/2 = (187207863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187207863:ℝ)/42188800) = (2021041:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187207863:ℝ)/42188800)-4 = (18452663:ℝ)/42188800 by norm_num]
    exact paid_terminal_692
  · change terminalPayment 693 ≤ terminalValue ((point cut hi 1024 693+point cut hi 1024 694)/2)
    have hp : terminalPayment 693 = (302663790456:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 693+point cut hi 1024 694)/2 = (187233013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187233013:ℝ)/42188800) = (2020035:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187233013:ℝ)/42188800)-4 = (18477813:ℝ)/42188800 by norm_num]
    exact paid_terminal_693
  · change terminalPayment 694 ≤ terminalValue ((point cut hi 1024 694+point cut hi 1024 695)/2)
    have hp : terminalPayment 694 = (301910683326:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 694+point cut hi 1024 695)/2 = (187258163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187258163:ℝ)/42188800) = (2019029:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187258163:ℝ)/42188800)-4 = (18502963:ℝ)/42188800 by norm_num]
    exact paid_terminal_694
  · change terminalPayment 695 ≤ terminalValue ((point cut hi 1024 695+point cut hi 1024 696)/2)
    have hp : terminalPayment 695 = (301156725915:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 695+point cut hi 1024 696)/2 = (187283313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187283313:ℝ)/42188800) = (2018023:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187283313:ℝ)/42188800)-4 = (18528113:ℝ)/42188800 by norm_num]
    exact paid_terminal_695
  · change terminalPayment 696 ≤ terminalValue ((point cut hi 1024 696+point cut hi 1024 697)/2)
    have hp : terminalPayment 696 = (300401917148:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 696+point cut hi 1024 697)/2 = (187308463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187308463:ℝ)/42188800) = (2017017:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187308463:ℝ)/42188800)-4 = (18553263:ℝ)/42188800 by norm_num]
    exact paid_terminal_696
  · change terminalPayment 697 ≤ terminalValue ((point cut hi 1024 697+point cut hi 1024 698)/2)
    have hp : terminalPayment 697 = (299646255943:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 697+point cut hi 1024 698)/2 = (187333613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187333613:ℝ)/42188800) = (2016011:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187333613:ℝ)/42188800)-4 = (18578413:ℝ)/42188800 by norm_num]
    exact paid_terminal_697
  · change terminalPayment 698 ≤ terminalValue ((point cut hi 1024 698+point cut hi 1024 699)/2)
    have hp : terminalPayment 698 = (298889741221:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 698+point cut hi 1024 699)/2 = (187358763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187358763:ℝ)/42188800) = (2015005:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187358763:ℝ)/42188800)-4 = (18603563:ℝ)/42188800 by norm_num]
    exact paid_terminal_698
  · change terminalPayment 699 ≤ terminalValue ((point cut hi 1024 699+point cut hi 1024 700)/2)
    have hp : terminalPayment 699 = (298132371899:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 699+point cut hi 1024 700)/2 = (187383913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187383913:ℝ)/42188800) = (2013999:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187383913:ℝ)/42188800)-4 = (18628713:ℝ)/42188800 by norm_num]
    exact paid_terminal_699
  · change terminalPayment 700 ≤ terminalValue ((point cut hi 1024 700+point cut hi 1024 701)/2)
    have hp : terminalPayment 700 = (297374146891:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 700+point cut hi 1024 701)/2 = (187409063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187409063:ℝ)/42188800) = (2012993:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187409063:ℝ)/42188800)-4 = (18653863:ℝ)/42188800 by norm_num]
    exact paid_terminal_700
  · change terminalPayment 701 ≤ terminalValue ((point cut hi 1024 701+point cut hi 1024 702)/2)
    have hp : terminalPayment 701 = (296615065112:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 701+point cut hi 1024 702)/2 = (187434213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187434213:ℝ)/42188800) = (2011987:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187434213:ℝ)/42188800)-4 = (18679013:ℝ)/42188800 by norm_num]
    exact paid_terminal_701
  · change terminalPayment 702 ≤ terminalValue ((point cut hi 1024 702+point cut hi 1024 703)/2)
    have hp : terminalPayment 702 = (295855125472:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 702+point cut hi 1024 703)/2 = (187459363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187459363:ℝ)/42188800) = (2010981:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187459363:ℝ)/42188800)-4 = (18704163:ℝ)/42188800 by norm_num]
    exact paid_terminal_702
  · change terminalPayment 703 ≤ terminalValue ((point cut hi 1024 703+point cut hi 1024 704)/2)
    have hp : terminalPayment 703 = (295094326881:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 703+point cut hi 1024 704)/2 = (187484513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187484513:ℝ)/42188800) = (2009975:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187484513:ℝ)/42188800)-4 = (18729313:ℝ)/42188800 by norm_num]
    exact paid_terminal_703
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_043
