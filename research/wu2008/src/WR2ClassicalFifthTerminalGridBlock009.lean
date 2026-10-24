import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints009
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_009 (j : Fin 16) : terminalPayment (16*9+j.val) ≤
    terminalValue ((point cut hi 1024 (16*9+j.val)+point cut hi 1024 (16*9+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 144 ≤ terminalValue ((point cut hi 1024 144+point cut hi 1024 145)/2)
    have hp : terminalPayment 144 = (611782629183:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 144+point cut hi 1024 145)/2 = (173425663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173425663:ℝ)/42188800) = (2572329:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173425663:ℝ)/42188800)-4 = (4670463:ℝ)/42188800 by norm_num]
    exact paid_terminal_144
  · change terminalPayment 145 ≤ terminalValue ((point cut hi 1024 145+point cut hi 1024 146)/2)
    have hp : terminalPayment 145 = (611374161838:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 145+point cut hi 1024 146)/2 = (173450813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173450813:ℝ)/42188800) = (2571323:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173450813:ℝ)/42188800)-4 = (4695613:ℝ)/42188800 by norm_num]
    exact paid_terminal_145
  · change terminalPayment 146 ≤ terminalValue ((point cut hi 1024 146+point cut hi 1024 147)/2)
    have hp : terminalPayment 146 = (610965230553:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 146+point cut hi 1024 147)/2 = (173475963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173475963:ℝ)/42188800) = (2570317:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173475963:ℝ)/42188800)-4 = (4720763:ℝ)/42188800 by norm_num]
    exact paid_terminal_146
  · change terminalPayment 147 ≤ terminalValue ((point cut hi 1024 147+point cut hi 1024 148)/2)
    have hp : terminalPayment 147 = (610555834895:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 147+point cut hi 1024 148)/2 = (173501113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173501113:ℝ)/42188800) = (2569311:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173501113:ℝ)/42188800)-4 = (4745913:ℝ)/42188800 by norm_num]
    exact paid_terminal_147
  · change terminalPayment 148 ≤ terminalValue ((point cut hi 1024 148+point cut hi 1024 149)/2)
    have hp : terminalPayment 148 = (610145974435:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 148+point cut hi 1024 149)/2 = (1684721:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((1684721:ℝ)/409600) = (24935:ℝ)/16384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((1684721:ℝ)/409600)-4 = (46321:ℝ)/409600 by norm_num]
    exact paid_terminal_148
  · change terminalPayment 149 ≤ terminalValue ((point cut hi 1024 149+point cut hi 1024 150)/2)
    have hp : terminalPayment 149 = (609735648740:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 149+point cut hi 1024 150)/2 = (173551413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173551413:ℝ)/42188800) = (2567299:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173551413:ℝ)/42188800)-4 = (4796213:ℝ)/42188800 by norm_num]
    exact paid_terminal_149
  · change terminalPayment 150 ≤ terminalValue ((point cut hi 1024 150+point cut hi 1024 151)/2)
    have hp : terminalPayment 150 = (609324857380:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 150+point cut hi 1024 151)/2 = (173576563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173576563:ℝ)/42188800) = (2566293:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173576563:ℝ)/42188800)-4 = (4821363:ℝ)/42188800 by norm_num]
    exact paid_terminal_150
  · change terminalPayment 151 ≤ terminalValue ((point cut hi 1024 151+point cut hi 1024 152)/2)
    have hp : terminalPayment 151 = (608913599919:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 151+point cut hi 1024 152)/2 = (173601713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173601713:ℝ)/42188800) = (2565287:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173601713:ℝ)/42188800)-4 = (4846513:ℝ)/42188800 by norm_num]
    exact paid_terminal_151
  · change terminalPayment 152 ≤ terminalValue ((point cut hi 1024 152+point cut hi 1024 153)/2)
    have hp : terminalPayment 152 = (608501875925:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 152+point cut hi 1024 153)/2 = (173626863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173626863:ℝ)/42188800) = (2564281:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173626863:ℝ)/42188800)-4 = (4871663:ℝ)/42188800 by norm_num]
    exact paid_terminal_152
  · change terminalPayment 153 ≤ terminalValue ((point cut hi 1024 153+point cut hi 1024 154)/2)
    have hp : terminalPayment 153 = (608089684962:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 153+point cut hi 1024 154)/2 = (173652013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173652013:ℝ)/42188800) = (2563275:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173652013:ℝ)/42188800)-4 = (4896813:ℝ)/42188800 by norm_num]
    exact paid_terminal_153
  · change terminalPayment 154 ≤ terminalValue ((point cut hi 1024 154+point cut hi 1024 155)/2)
    have hp : terminalPayment 154 = (607677026596:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 154+point cut hi 1024 155)/2 = (173677163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173677163:ℝ)/42188800) = (2562269:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173677163:ℝ)/42188800)-4 = (4921963:ℝ)/42188800 by norm_num]
    exact paid_terminal_154
  · change terminalPayment 155 ≤ terminalValue ((point cut hi 1024 155+point cut hi 1024 156)/2)
    have hp : terminalPayment 155 = (607263900391:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 155+point cut hi 1024 156)/2 = (173702313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173702313:ℝ)/42188800) = (2561263:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173702313:ℝ)/42188800)-4 = (4947113:ℝ)/42188800 by norm_num]
    exact paid_terminal_155
  · change terminalPayment 156 ≤ terminalValue ((point cut hi 1024 156+point cut hi 1024 157)/2)
    have hp : terminalPayment 156 = (606850305908:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 156+point cut hi 1024 157)/2 = (173727463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173727463:ℝ)/42188800) = (2560257:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173727463:ℝ)/42188800)-4 = (4972263:ℝ)/42188800 by norm_num]
    exact paid_terminal_156
  · change terminalPayment 157 ≤ terminalValue ((point cut hi 1024 157+point cut hi 1024 158)/2)
    have hp : terminalPayment 157 = (606436242712:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 157+point cut hi 1024 158)/2 = (173752613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173752613:ℝ)/42188800) = (2559251:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173752613:ℝ)/42188800)-4 = (4997413:ℝ)/42188800 by norm_num]
    exact paid_terminal_157
  · change terminalPayment 158 ≤ terminalValue ((point cut hi 1024 158+point cut hi 1024 159)/2)
    have hp : terminalPayment 158 = (606021710363:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 158+point cut hi 1024 159)/2 = (173777763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173777763:ℝ)/42188800) = (2558245:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173777763:ℝ)/42188800)-4 = (5022563:ℝ)/42188800 by norm_num]
    exact paid_terminal_158
  · change terminalPayment 159 ≤ terminalValue ((point cut hi 1024 159+point cut hi 1024 160)/2)
    have hp : terminalPayment 159 = (605606708422:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 159+point cut hi 1024 160)/2 = (173802913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173802913:ℝ)/42188800) = (2557239:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173802913:ℝ)/42188800)-4 = (5047713:ℝ)/42188800 by norm_num]
    exact paid_terminal_159
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_009
