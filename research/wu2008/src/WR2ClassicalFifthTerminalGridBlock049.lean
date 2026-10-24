import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints049
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_049 (j : Fin 16) : terminalPayment (16*49+j.val) ≤
    terminalValue ((point cut hi 1024 (16*49+j.val)+point cut hi 1024 (16*49+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 784 ≤ terminalValue ((point cut hi 1024 784+point cut hi 1024 785)/2)
    have hp : terminalPayment 784 = (230513129382:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 784+point cut hi 1024 785)/2 = (189521663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189521663:ℝ)/42188800) = (1928489:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189521663:ℝ)/42188800)-4 = (20766463:ℝ)/42188800 by norm_num]
    exact paid_terminal_784
  · change terminalPayment 785 ≤ terminalValue ((point cut hi 1024 785+point cut hi 1024 786)/2)
    have hp : terminalPayment 785 = (229677999453:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 785+point cut hi 1024 786)/2 = (189546813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189546813:ℝ)/42188800) = (1927483:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189546813:ℝ)/42188800)-4 = (20791613:ℝ)/42188800 by norm_num]
    exact paid_terminal_785
  · change terminalPayment 786 ≤ terminalValue ((point cut hi 1024 786+point cut hi 1024 787)/2)
    have hp : terminalPayment 786 = (228841913138:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 786+point cut hi 1024 787)/2 = (189571963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189571963:ℝ)/42188800) = (1926477:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189571963:ℝ)/42188800)-4 = (20816763:ℝ)/42188800 by norm_num]
    exact paid_terminal_786
  · change terminalPayment 787 ≤ terminalValue ((point cut hi 1024 787+point cut hi 1024 788)/2)
    have hp : terminalPayment 787 = (228004869174:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 787+point cut hi 1024 788)/2 = (189597113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189597113:ℝ)/42188800) = (1925471:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189597113:ℝ)/42188800)-4 = (20841913:ℝ)/42188800 by norm_num]
    exact paid_terminal_787
  · change terminalPayment 788 ≤ terminalValue ((point cut hi 1024 788+point cut hi 1024 789)/2)
    have hp : terminalPayment 788 = (227166866298:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 788+point cut hi 1024 789)/2 = (189622263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189622263:ℝ)/42188800) = (1924465:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189622263:ℝ)/42188800)-4 = (20867063:ℝ)/42188800 by norm_num]
    exact paid_terminal_788
  · change terminalPayment 789 ≤ terminalValue ((point cut hi 1024 789+point cut hi 1024 790)/2)
    have hp : terminalPayment 789 = (226327903243:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 789+point cut hi 1024 790)/2 = (189647413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189647413:ℝ)/42188800) = (1923459:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189647413:ℝ)/42188800)-4 = (20892213:ℝ)/42188800 by norm_num]
    exact paid_terminal_789
  · change terminalPayment 790 ≤ terminalValue ((point cut hi 1024 790+point cut hi 1024 791)/2)
    have hp : terminalPayment 790 = (225487978738:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 790+point cut hi 1024 791)/2 = (189672563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189672563:ℝ)/42188800) = (1922453:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189672563:ℝ)/42188800)-4 = (20917363:ℝ)/42188800 by norm_num]
    exact paid_terminal_790
  · change terminalPayment 791 ≤ terminalValue ((point cut hi 1024 791+point cut hi 1024 792)/2)
    have hp : terminalPayment 791 = (224647091514:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 791+point cut hi 1024 792)/2 = (189697713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189697713:ℝ)/42188800) = (1921447:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189697713:ℝ)/42188800)-4 = (20942513:ℝ)/42188800 by norm_num]
    exact paid_terminal_791
  · change terminalPayment 792 ≤ terminalValue ((point cut hi 1024 792+point cut hi 1024 793)/2)
    have hp : terminalPayment 792 = (223805240296:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 792+point cut hi 1024 793)/2 = (189722863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189722863:ℝ)/42188800) = (1920441:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189722863:ℝ)/42188800)-4 = (20967663:ℝ)/42188800 by norm_num]
    exact paid_terminal_792
  · change terminalPayment 793 ≤ terminalValue ((point cut hi 1024 793+point cut hi 1024 794)/2)
    have hp : terminalPayment 793 = (222962423809:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 793+point cut hi 1024 794)/2 = (189748013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189748013:ℝ)/42188800) = (1919435:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189748013:ℝ)/42188800)-4 = (20992813:ℝ)/42188800 by norm_num]
    exact paid_terminal_793
  · change terminalPayment 794 ≤ terminalValue ((point cut hi 1024 794+point cut hi 1024 795)/2)
    have hp : terminalPayment 794 = (222118640775:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 794+point cut hi 1024 795)/2 = (189773163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189773163:ℝ)/42188800) = (1918429:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189773163:ℝ)/42188800)-4 = (21017963:ℝ)/42188800 by norm_num]
    exact paid_terminal_794
  · change terminalPayment 795 ≤ terminalValue ((point cut hi 1024 795+point cut hi 1024 796)/2)
    have hp : terminalPayment 795 = (221273889912:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 795+point cut hi 1024 796)/2 = (189798313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189798313:ℝ)/42188800) = (1917423:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189798313:ℝ)/42188800)-4 = (21043113:ℝ)/42188800 by norm_num]
    exact paid_terminal_795
  · change terminalPayment 796 ≤ terminalValue ((point cut hi 1024 796+point cut hi 1024 797)/2)
    have hp : terminalPayment 796 = (220428169940:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 796+point cut hi 1024 797)/2 = (189823463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189823463:ℝ)/42188800) = (1916417:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189823463:ℝ)/42188800)-4 = (21068263:ℝ)/42188800 by norm_num]
    exact paid_terminal_796
  · change terminalPayment 797 ≤ terminalValue ((point cut hi 1024 797+point cut hi 1024 798)/2)
    have hp : terminalPayment 797 = (219581479572:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 797+point cut hi 1024 798)/2 = (189848613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189848613:ℝ)/42188800) = (1915411:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189848613:ℝ)/42188800)-4 = (21093413:ℝ)/42188800 by norm_num]
    exact paid_terminal_797
  · change terminalPayment 798 ≤ terminalValue ((point cut hi 1024 798+point cut hi 1024 799)/2)
    have hp : terminalPayment 798 = (218733817522:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 798+point cut hi 1024 799)/2 = (189873763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189873763:ℝ)/42188800) = (1914405:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189873763:ℝ)/42188800)-4 = (21118563:ℝ)/42188800 by norm_num]
    exact paid_terminal_798
  · change terminalPayment 799 ≤ terminalValue ((point cut hi 1024 799+point cut hi 1024 800)/2)
    have hp : terminalPayment 799 = (217885182500:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 799+point cut hi 1024 800)/2 = (189898913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189898913:ℝ)/42188800) = (1913399:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189898913:ℝ)/42188800)-4 = (21143713:ℝ)/42188800 by norm_num]
    exact paid_terminal_799
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_049
