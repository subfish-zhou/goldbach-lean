import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints058
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_058 (j : Fin 16) : terminalPayment (16*58+j.val) ≤
    terminalValue ((point cut hi 1024 (16*58+j.val)+point cut hi 1024 (16*58+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 928 ≤ terminalValue ((point cut hi 1024 928+point cut hi 1024 929)/2)
    have hp : terminalPayment 928 = (99751591060:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 928+point cut hi 1024 929)/2 = (193143263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193143263:ℝ)/42188800) = (1783625:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193143263:ℝ)/42188800)-4 = (24388063:ℝ)/42188800 by norm_num]
    exact paid_terminal_928
  · change terminalPayment 929 ≤ terminalValue ((point cut hi 1024 929+point cut hi 1024 930)/2)
    have hp : terminalPayment 929 = (98764571839:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 929+point cut hi 1024 930)/2 = (193168413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193168413:ℝ)/42188800) = (1782619:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193168413:ℝ)/42188800)-4 = (24413213:ℝ)/42188800 by norm_num]
    exact paid_terminal_929
  · change terminalPayment 930 ≤ terminalValue ((point cut hi 1024 930+point cut hi 1024 931)/2)
    have hp : terminalPayment 930 = (97776389011:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 930+point cut hi 1024 931)/2 = (193193563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193193563:ℝ)/42188800) = (1781613:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193193563:ℝ)/42188800)-4 = (24438363:ℝ)/42188800 by norm_num]
    exact paid_terminal_930
  · change terminalPayment 931 ≤ terminalValue ((point cut hi 1024 931+point cut hi 1024 932)/2)
    have hp : terminalPayment 931 = (96787040940:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 931+point cut hi 1024 932)/2 = (193218713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193218713:ℝ)/42188800) = (1780607:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193218713:ℝ)/42188800)-4 = (24463513:ℝ)/42188800 by norm_num]
    exact paid_terminal_931
  · change terminalPayment 932 ≤ terminalValue ((point cut hi 1024 932+point cut hi 1024 933)/2)
    have hp : terminalPayment 932 = (95796525984:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 932+point cut hi 1024 933)/2 = (193243863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193243863:ℝ)/42188800) = (1779601:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193243863:ℝ)/42188800)-4 = (24488663:ℝ)/42188800 by norm_num]
    exact paid_terminal_932
  · change terminalPayment 933 ≤ terminalValue ((point cut hi 1024 933+point cut hi 1024 934)/2)
    have hp : terminalPayment 933 = (94804842499:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 933+point cut hi 1024 934)/2 = (193269013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193269013:ℝ)/42188800) = (1778595:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193269013:ℝ)/42188800)-4 = (24513813:ℝ)/42188800 by norm_num]
    exact paid_terminal_933
  · change terminalPayment 934 ≤ terminalValue ((point cut hi 1024 934+point cut hi 1024 935)/2)
    have hp : terminalPayment 934 = (93811988839:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 934+point cut hi 1024 935)/2 = (193294163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193294163:ℝ)/42188800) = (1777589:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193294163:ℝ)/42188800)-4 = (24538963:ℝ)/42188800 by norm_num]
    exact paid_terminal_934
  · change terminalPayment 935 ≤ terminalValue ((point cut hi 1024 935+point cut hi 1024 936)/2)
    have hp : terminalPayment 935 = (92817963354:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 935+point cut hi 1024 936)/2 = (193319313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193319313:ℝ)/42188800) = (1776583:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193319313:ℝ)/42188800)-4 = (24564113:ℝ)/42188800 by norm_num]
    exact paid_terminal_935
  · change terminalPayment 936 ≤ terminalValue ((point cut hi 1024 936+point cut hi 1024 937)/2)
    have hp : terminalPayment 936 = (91822764391:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 936+point cut hi 1024 937)/2 = (193344463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193344463:ℝ)/42188800) = (1775577:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193344463:ℝ)/42188800)-4 = (24589263:ℝ)/42188800 by norm_num]
    exact paid_terminal_936
  · change terminalPayment 937 ≤ terminalValue ((point cut hi 1024 937+point cut hi 1024 938)/2)
    have hp : terminalPayment 937 = (90826390294:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 937+point cut hi 1024 938)/2 = (193369613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193369613:ℝ)/42188800) = (1774571:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193369613:ℝ)/42188800)-4 = (24614413:ℝ)/42188800 by norm_num]
    exact paid_terminal_937
  · change terminalPayment 938 ≤ terminalValue ((point cut hi 1024 938+point cut hi 1024 939)/2)
    have hp : terminalPayment 938 = (89828839404:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 938+point cut hi 1024 939)/2 = (193394763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193394763:ℝ)/42188800) = (1773565:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193394763:ℝ)/42188800)-4 = (24639563:ℝ)/42188800 by norm_num]
    exact paid_terminal_938
  · change terminalPayment 939 ≤ terminalValue ((point cut hi 1024 939+point cut hi 1024 940)/2)
    have hp : terminalPayment 939 = (88830110058:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 939+point cut hi 1024 940)/2 = (193419913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193419913:ℝ)/42188800) = (1772559:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193419913:ℝ)/42188800)-4 = (24664713:ℝ)/42188800 by norm_num]
    exact paid_terminal_939
  · change terminalPayment 940 ≤ terminalValue ((point cut hi 1024 940+point cut hi 1024 941)/2)
    have hp : terminalPayment 940 = (87830200591:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 940+point cut hi 1024 941)/2 = (193445063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193445063:ℝ)/42188800) = (1771553:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193445063:ℝ)/42188800)-4 = (24689863:ℝ)/42188800 by norm_num]
    exact paid_terminal_940
  · change terminalPayment 941 ≤ terminalValue ((point cut hi 1024 941+point cut hi 1024 942)/2)
    have hp : terminalPayment 941 = (86829109335:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 941+point cut hi 1024 942)/2 = (193470213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193470213:ℝ)/42188800) = (1770547:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193470213:ℝ)/42188800)-4 = (24715013:ℝ)/42188800 by norm_num]
    exact paid_terminal_941
  · change terminalPayment 942 ≤ terminalValue ((point cut hi 1024 942+point cut hi 1024 943)/2)
    have hp : terminalPayment 942 = (85826834618:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 942+point cut hi 1024 943)/2 = (193495363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193495363:ℝ)/42188800) = (1769541:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193495363:ℝ)/42188800)-4 = (24740163:ℝ)/42188800 by norm_num]
    exact paid_terminal_942
  · change terminalPayment 943 ≤ terminalValue ((point cut hi 1024 943+point cut hi 1024 944)/2)
    have hp : terminalPayment 943 = (84823374767:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 943+point cut hi 1024 944)/2 = (193520513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193520513:ℝ)/42188800) = (1768535:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193520513:ℝ)/42188800)-4 = (24765313:ℝ)/42188800 by norm_num]
    exact paid_terminal_943
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_058
