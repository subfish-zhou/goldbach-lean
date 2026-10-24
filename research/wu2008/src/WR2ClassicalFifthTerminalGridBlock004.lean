import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints004
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_004 (j : Fin 16) : terminalPayment (16*4+j.val) ≤
    terminalValue ((point cut hi 1024 (16*4+j.val)+point cut hi 1024 (16*4+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 64 ≤ terminalValue ((point cut hi 1024 64+point cut hi 1024 65)/2)
    have hp : terminalPayment 64 = (642993608166:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 64+point cut hi 1024 65)/2 = (171413663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171413663:ℝ)/42188800) = (2652809:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171413663:ℝ)/42188800)-4 = (2658463:ℝ)/42188800 by norm_num]
    exact paid_terminal_64
  · change terminalPayment 65 ≤ terminalValue ((point cut hi 1024 65+point cut hi 1024 66)/2)
    have hp : terminalPayment 65 = (642620926352:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 65+point cut hi 1024 66)/2 = (171438813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171438813:ℝ)/42188800) = (2651803:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171438813:ℝ)/42188800)-4 = (2683613:ℝ)/42188800 by norm_num]
    exact paid_terminal_65
  · change terminalPayment 66 ≤ terminalValue ((point cut hi 1024 66+point cut hi 1024 67)/2)
    have hp : terminalPayment 66 = (642247812690:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 66+point cut hi 1024 67)/2 = (171463963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171463963:ℝ)/42188800) = (2650797:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171463963:ℝ)/42188800)-4 = (2708763:ℝ)/42188800 by norm_num]
    exact paid_terminal_66
  · change terminalPayment 67 ≤ terminalValue ((point cut hi 1024 67+point cut hi 1024 68)/2)
    have hp : terminalPayment 67 = (641874266806:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 67+point cut hi 1024 68)/2 = (171489113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171489113:ℝ)/42188800) = (2649791:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171489113:ℝ)/42188800)-4 = (2733913:ℝ)/42188800 by norm_num]
    exact paid_terminal_67
  · change terminalPayment 68 ≤ terminalValue ((point cut hi 1024 68+point cut hi 1024 69)/2)
    have hp : terminalPayment 68 = (641500288325:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 68+point cut hi 1024 69)/2 = (171514263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171514263:ℝ)/42188800) = (2648785:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171514263:ℝ)/42188800)-4 = (2759063:ℝ)/42188800 by norm_num]
    exact paid_terminal_68
  · change terminalPayment 69 ≤ terminalValue ((point cut hi 1024 69+point cut hi 1024 70)/2)
    have hp : terminalPayment 69 = (641125876872:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 69+point cut hi 1024 70)/2 = (171539413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171539413:ℝ)/42188800) = (2647779:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171539413:ℝ)/42188800)-4 = (2784213:ℝ)/42188800 by norm_num]
    exact paid_terminal_69
  · change terminalPayment 70 ≤ terminalValue ((point cut hi 1024 70+point cut hi 1024 71)/2)
    have hp : terminalPayment 70 = (640751032071:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 70+point cut hi 1024 71)/2 = (171564563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171564563:ℝ)/42188800) = (2646773:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171564563:ℝ)/42188800)-4 = (2809363:ℝ)/42188800 by norm_num]
    exact paid_terminal_70
  · change terminalPayment 71 ≤ terminalValue ((point cut hi 1024 71+point cut hi 1024 72)/2)
    have hp : terminalPayment 71 = (640375753547:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 71+point cut hi 1024 72)/2 = (171589713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171589713:ℝ)/42188800) = (2645767:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171589713:ℝ)/42188800)-4 = (2834513:ℝ)/42188800 by norm_num]
    exact paid_terminal_71
  · change terminalPayment 72 ≤ terminalValue ((point cut hi 1024 72+point cut hi 1024 73)/2)
    have hp : terminalPayment 72 = (640000040920:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 72+point cut hi 1024 73)/2 = (171614863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171614863:ℝ)/42188800) = (2644761:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171614863:ℝ)/42188800)-4 = (2859663:ℝ)/42188800 by norm_num]
    exact paid_terminal_72
  · change terminalPayment 73 ≤ terminalValue ((point cut hi 1024 73+point cut hi 1024 74)/2)
    have hp : terminalPayment 73 = (639623893815:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 73+point cut hi 1024 74)/2 = (171640013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171640013:ℝ)/42188800) = (2643755:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171640013:ℝ)/42188800)-4 = (2884813:ℝ)/42188800 by norm_num]
    exact paid_terminal_73
  · change terminalPayment 74 ≤ terminalValue ((point cut hi 1024 74+point cut hi 1024 75)/2)
    have hp : terminalPayment 74 = (639247311851:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 74+point cut hi 1024 75)/2 = (171665163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171665163:ℝ)/42188800) = (2642749:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171665163:ℝ)/42188800)-4 = (2909963:ℝ)/42188800 by norm_num]
    exact paid_terminal_74
  · change terminalPayment 75 ≤ terminalValue ((point cut hi 1024 75+point cut hi 1024 76)/2)
    have hp : terminalPayment 75 = (638870294651:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 75+point cut hi 1024 76)/2 = (171690313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171690313:ℝ)/42188800) = (2641743:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171690313:ℝ)/42188800)-4 = (2935113:ℝ)/42188800 by norm_num]
    exact paid_terminal_75
  · change terminalPayment 76 ≤ terminalValue ((point cut hi 1024 76+point cut hi 1024 77)/2)
    have hp : terminalPayment 76 = (638492841833:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 76+point cut hi 1024 77)/2 = (171715463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171715463:ℝ)/42188800) = (2640737:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171715463:ℝ)/42188800)-4 = (2960263:ℝ)/42188800 by norm_num]
    exact paid_terminal_76
  · change terminalPayment 77 ≤ terminalValue ((point cut hi 1024 77+point cut hi 1024 78)/2)
    have hp : terminalPayment 77 = (638114953019:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 77+point cut hi 1024 78)/2 = (171740613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171740613:ℝ)/42188800) = (2639731:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171740613:ℝ)/42188800)-4 = (2985413:ℝ)/42188800 by norm_num]
    exact paid_terminal_77
  · change terminalPayment 78 ≤ terminalValue ((point cut hi 1024 78+point cut hi 1024 79)/2)
    have hp : terminalPayment 78 = (637736627825:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 78+point cut hi 1024 79)/2 = (171765763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171765763:ℝ)/42188800) = (2638725:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171765763:ℝ)/42188800)-4 = (3010563:ℝ)/42188800 by norm_num]
    exact paid_terminal_78
  · change terminalPayment 79 ≤ terminalValue ((point cut hi 1024 79+point cut hi 1024 80)/2)
    have hp : terminalPayment 79 = (637357865872:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 79+point cut hi 1024 80)/2 = (171790913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171790913:ℝ)/42188800) = (2637719:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171790913:ℝ)/42188800)-4 = (3035713:ℝ)/42188800 by norm_num]
    exact paid_terminal_79
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_004
