import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints007
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_007 (j : Fin 16) : terminalPayment (16*7+j.val) ≤
    terminalValue ((point cut hi 1024 (16*7+j.val)+point cut hi 1024 (16*7+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 112 ≤ terminalValue ((point cut hi 1024 112+point cut hi 1024 113)/2)
    have hp : terminalPayment 112 = (624611158735:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 112+point cut hi 1024 113)/2 = (172620863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172620863:ℝ)/42188800) = (2604521:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172620863:ℝ)/42188800)-4 = (3865663:ℝ)/42188800 by norm_num]
    exact paid_terminal_112
  · change terminalPayment 113 ≤ terminalValue ((point cut hi 1024 113+point cut hi 1024 114)/2)
    have hp : terminalPayment 113 = (624217314778:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 113+point cut hi 1024 114)/2 = (172646013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172646013:ℝ)/42188800) = (2603515:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172646013:ℝ)/42188800)-4 = (3890813:ℝ)/42188800 by norm_num]
    exact paid_terminal_113
  · change terminalPayment 114 ≤ terminalValue ((point cut hi 1024 114+point cut hi 1024 115)/2)
    have hp : terminalPayment 114 = (623823020260:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 114+point cut hi 1024 115)/2 = (172671163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172671163:ℝ)/42188800) = (2602509:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172671163:ℝ)/42188800)-4 = (3915963:ℝ)/42188800 by norm_num]
    exact paid_terminal_114
  · change terminalPayment 115 ≤ terminalValue ((point cut hi 1024 115+point cut hi 1024 116)/2)
    have hp : terminalPayment 115 = (623428274773:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 115+point cut hi 1024 116)/2 = (172696313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172696313:ℝ)/42188800) = (2601503:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172696313:ℝ)/42188800)-4 = (3941113:ℝ)/42188800 by norm_num]
    exact paid_terminal_115
  · change terminalPayment 116 ≤ terminalValue ((point cut hi 1024 116+point cut hi 1024 117)/2)
    have hp : terminalPayment 116 = (623033077909:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 116+point cut hi 1024 117)/2 = (172721463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172721463:ℝ)/42188800) = (2600497:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172721463:ℝ)/42188800)-4 = (3966263:ℝ)/42188800 by norm_num]
    exact paid_terminal_116
  · change terminalPayment 117 ≤ terminalValue ((point cut hi 1024 117+point cut hi 1024 118)/2)
    have hp : terminalPayment 117 = (622637429260:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 117+point cut hi 1024 118)/2 = (172746613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172746613:ℝ)/42188800) = (2599491:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172746613:ℝ)/42188800)-4 = (3991413:ℝ)/42188800 by norm_num]
    exact paid_terminal_117
  · change terminalPayment 118 ≤ terminalValue ((point cut hi 1024 118+point cut hi 1024 119)/2)
    have hp : terminalPayment 118 = (622241328418:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 118+point cut hi 1024 119)/2 = (172771763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172771763:ℝ)/42188800) = (2598485:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172771763:ℝ)/42188800)-4 = (4016563:ℝ)/42188800 by norm_num]
    exact paid_terminal_118
  · change terminalPayment 119 ≤ terminalValue ((point cut hi 1024 119+point cut hi 1024 120)/2)
    have hp : terminalPayment 119 = (621844774971:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 119+point cut hi 1024 120)/2 = (172796913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172796913:ℝ)/42188800) = (2597479:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172796913:ℝ)/42188800)-4 = (4041713:ℝ)/42188800 by norm_num]
    exact paid_terminal_119
  · change terminalPayment 120 ≤ terminalValue ((point cut hi 1024 120+point cut hi 1024 121)/2)
    have hp : terminalPayment 120 = (621447768510:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 120+point cut hi 1024 121)/2 = (172822063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172822063:ℝ)/42188800) = (2596473:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172822063:ℝ)/42188800)-4 = (4066863:ℝ)/42188800 by norm_num]
    exact paid_terminal_120
  · change terminalPayment 121 ≤ terminalValue ((point cut hi 1024 121+point cut hi 1024 122)/2)
    have hp : terminalPayment 121 = (621050308623:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 121+point cut hi 1024 122)/2 = (172847213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172847213:ℝ)/42188800) = (2595467:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172847213:ℝ)/42188800)-4 = (4092013:ℝ)/42188800 by norm_num]
    exact paid_terminal_121
  · change terminalPayment 122 ≤ terminalValue ((point cut hi 1024 122+point cut hi 1024 123)/2)
    have hp : terminalPayment 122 = (620652394899:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 122+point cut hi 1024 123)/2 = (172872363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172872363:ℝ)/42188800) = (2594461:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172872363:ℝ)/42188800)-4 = (4117163:ℝ)/42188800 by norm_num]
    exact paid_terminal_122
  · change terminalPayment 123 ≤ terminalValue ((point cut hi 1024 123+point cut hi 1024 124)/2)
    have hp : terminalPayment 123 = (620254026924:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 123+point cut hi 1024 124)/2 = (172897513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172897513:ℝ)/42188800) = (2593455:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172897513:ℝ)/42188800)-4 = (4142313:ℝ)/42188800 by norm_num]
    exact paid_terminal_123
  · change terminalPayment 124 ≤ terminalValue ((point cut hi 1024 124+point cut hi 1024 125)/2)
    have hp : terminalPayment 124 = (619855204286:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 124+point cut hi 1024 125)/2 = (172922663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172922663:ℝ)/42188800) = (2592449:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172922663:ℝ)/42188800)-4 = (4167463:ℝ)/42188800 by norm_num]
    exact paid_terminal_124
  · change terminalPayment 125 ≤ terminalValue ((point cut hi 1024 125+point cut hi 1024 126)/2)
    have hp : terminalPayment 125 = (619455926571:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 125+point cut hi 1024 126)/2 = (172947813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172947813:ℝ)/42188800) = (2591443:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172947813:ℝ)/42188800)-4 = (4192613:ℝ)/42188800 by norm_num]
    exact paid_terminal_125
  · change terminalPayment 126 ≤ terminalValue ((point cut hi 1024 126+point cut hi 1024 127)/2)
    have hp : terminalPayment 126 = (619056193363:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 126+point cut hi 1024 127)/2 = (172972963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172972963:ℝ)/42188800) = (2590437:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172972963:ℝ)/42188800)-4 = (4217763:ℝ)/42188800 by norm_num]
    exact paid_terminal_126
  · change terminalPayment 127 ≤ terminalValue ((point cut hi 1024 127+point cut hi 1024 128)/2)
    have hp : terminalPayment 127 = (618656004247:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 127+point cut hi 1024 128)/2 = (172998113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((172998113:ℝ)/42188800) = (2589431:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((172998113:ℝ)/42188800)-4 = (4242913:ℝ)/42188800 by norm_num]
    exact paid_terminal_127
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_007
