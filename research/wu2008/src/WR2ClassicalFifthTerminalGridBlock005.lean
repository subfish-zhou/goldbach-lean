import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints005
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_005 (j : Fin 16) : terminalPayment (16*5+j.val) ≤
    terminalValue ((point cut hi 1024 (16*5+j.val)+point cut hi 1024 (16*5+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 80 ≤ terminalValue ((point cut hi 1024 80+point cut hi 1024 81)/2)
    have hp : terminalPayment 80 = (636978666775:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 80+point cut hi 1024 81)/2 = (171816063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171816063:ℝ)/42188800) = (2636713:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171816063:ℝ)/42188800)-4 = (3060863:ℝ)/42188800 by norm_num]
    exact paid_terminal_80
  · change terminalPayment 81 ≤ terminalValue ((point cut hi 1024 81+point cut hi 1024 82)/2)
    have hp : terminalPayment 81 = (636599030151:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 81+point cut hi 1024 82)/2 = (171841213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171841213:ℝ)/42188800) = (2635707:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171841213:ℝ)/42188800)-4 = (3086013:ℝ)/42188800 by norm_num]
    exact paid_terminal_81
  · change terminalPayment 82 ≤ terminalValue ((point cut hi 1024 82+point cut hi 1024 83)/2)
    have hp : terminalPayment 82 = (636218955617:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 82+point cut hi 1024 83)/2 = (171866363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171866363:ℝ)/42188800) = (2634701:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171866363:ℝ)/42188800)-4 = (3111163:ℝ)/42188800 by norm_num]
    exact paid_terminal_82
  · change terminalPayment 83 ≤ terminalValue ((point cut hi 1024 83+point cut hi 1024 84)/2)
    have hp : terminalPayment 83 = (635838442789:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 83+point cut hi 1024 84)/2 = (171891513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171891513:ℝ)/42188800) = (2633695:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171891513:ℝ)/42188800)-4 = (3136313:ℝ)/42188800 by norm_num]
    exact paid_terminal_83
  · change terminalPayment 84 ≤ terminalValue ((point cut hi 1024 84+point cut hi 1024 85)/2)
    have hp : terminalPayment 84 = (635457491279:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 84+point cut hi 1024 85)/2 = (171916663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171916663:ℝ)/42188800) = (2632689:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171916663:ℝ)/42188800)-4 = (3161463:ℝ)/42188800 by norm_num]
    exact paid_terminal_84
  · change terminalPayment 85 ≤ terminalValue ((point cut hi 1024 85+point cut hi 1024 86)/2)
    have hp : terminalPayment 85 = (635076100704:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 85+point cut hi 1024 86)/2 = (171941813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171941813:ℝ)/42188800) = (2631683:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171941813:ℝ)/42188800)-4 = (3186613:ℝ)/42188800 by norm_num]
    exact paid_terminal_85
  · change terminalPayment 86 ≤ terminalValue ((point cut hi 1024 86+point cut hi 1024 87)/2)
    have hp : terminalPayment 86 = (634694270676:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 86+point cut hi 1024 87)/2 = (171966963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171966963:ℝ)/42188800) = (2630677:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171966963:ℝ)/42188800)-4 = (3211763:ℝ)/42188800 by norm_num]
    exact paid_terminal_86
  · change terminalPayment 87 ≤ terminalValue ((point cut hi 1024 87+point cut hi 1024 88)/2)
    have hp : terminalPayment 87 = (634312000807:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 87+point cut hi 1024 88)/2 = (171992113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171992113:ℝ)/42188800) = (2629671:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171992113:ℝ)/42188800)-4 = (3236913:ℝ)/42188800 by norm_num]
    exact paid_terminal_87
  · change terminalPayment 88 ≤ terminalValue ((point cut hi 1024 88+point cut hi 1024 89)/2)
    have hp : terminalPayment 88 = (633929290710:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 88+point cut hi 1024 89)/2 = (172017263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172017263:ℝ)/42188800) = (2628665:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172017263:ℝ)/42188800)-4 = (3262063:ℝ)/42188800 by norm_num]
    exact paid_terminal_88
  · change terminalPayment 89 ≤ terminalValue ((point cut hi 1024 89+point cut hi 1024 90)/2)
    have hp : terminalPayment 89 = (633546139995:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 89+point cut hi 1024 90)/2 = (172042413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172042413:ℝ)/42188800) = (2627659:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172042413:ℝ)/42188800)-4 = (3287213:ℝ)/42188800 by norm_num]
    exact paid_terminal_89
  · change terminalPayment 90 ≤ terminalValue ((point cut hi 1024 90+point cut hi 1024 91)/2)
    have hp : terminalPayment 90 = (633162548274:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 90+point cut hi 1024 91)/2 = (172067563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172067563:ℝ)/42188800) = (2626653:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172067563:ℝ)/42188800)-4 = (3312363:ℝ)/42188800 by norm_num]
    exact paid_terminal_90
  · change terminalPayment 91 ≤ terminalValue ((point cut hi 1024 91+point cut hi 1024 92)/2)
    have hp : terminalPayment 91 = (632778515156:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 91+point cut hi 1024 92)/2 = (172092713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172092713:ℝ)/42188800) = (2625647:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172092713:ℝ)/42188800)-4 = (3337513:ℝ)/42188800 by norm_num]
    exact paid_terminal_91
  · change terminalPayment 92 ≤ terminalValue ((point cut hi 1024 92+point cut hi 1024 93)/2)
    have hp : terminalPayment 92 = (632394040251:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 92+point cut hi 1024 93)/2 = (172117863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172117863:ℝ)/42188800) = (2624641:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172117863:ℝ)/42188800)-4 = (3362663:ℝ)/42188800 by norm_num]
    exact paid_terminal_92
  · change terminalPayment 93 ≤ terminalValue ((point cut hi 1024 93+point cut hi 1024 94)/2)
    have hp : terminalPayment 93 = (632009123166:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 93+point cut hi 1024 94)/2 = (172143013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172143013:ℝ)/42188800) = (2623635:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172143013:ℝ)/42188800)-4 = (3387813:ℝ)/42188800 by norm_num]
    exact paid_terminal_93
  · change terminalPayment 94 ≤ terminalValue ((point cut hi 1024 94+point cut hi 1024 95)/2)
    have hp : terminalPayment 94 = (631623763510:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 94+point cut hi 1024 95)/2 = (172168163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172168163:ℝ)/42188800) = (2622629:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172168163:ℝ)/42188800)-4 = (3412963:ℝ)/42188800 by norm_num]
    exact paid_terminal_94
  · change terminalPayment 95 ≤ terminalValue ((point cut hi 1024 95+point cut hi 1024 96)/2)
    have hp : terminalPayment 95 = (631237960890:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 95+point cut hi 1024 96)/2 = (172193313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172193313:ℝ)/42188800) = (2621623:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172193313:ℝ)/42188800)-4 = (3438113:ℝ)/42188800 by norm_num]
    exact paid_terminal_95
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_005
