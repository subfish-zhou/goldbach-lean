import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints012
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_012 (j : Fin 16) : terminalPayment (16*12+j.val) ≤
    terminalValue ((point cut hi 1024 (16*12+j.val)+point cut hi 1024 (16*12+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 192 ≤ terminalValue ((point cut hi 1024 192+point cut hi 1024 193)/2)
    have hp : terminalPayment 192 = (591645284610:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 192+point cut hi 1024 193)/2 = (174632863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174632863:ℝ)/42188800) = (2524041:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174632863:ℝ)/42188800)-4 = (5877663:ℝ)/42188800 by norm_num]
    exact paid_terminal_192
  · change terminalPayment 193 ≤ terminalValue ((point cut hi 1024 193+point cut hi 1024 194)/2)
    have hp : terminalPayment 193 = (591214049834:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 193+point cut hi 1024 194)/2 = (174658013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174658013:ℝ)/42188800) = (2523035:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174658013:ℝ)/42188800)-4 = (5902813:ℝ)/42188800 by norm_num]
    exact paid_terminal_193
  · change terminalPayment 194 ≤ terminalValue ((point cut hi 1024 194+point cut hi 1024 195)/2)
    have hp : terminalPayment 194 = (590782329615:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 194+point cut hi 1024 195)/2 = (174683163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174683163:ℝ)/42188800) = (2522029:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174683163:ℝ)/42188800)-4 = (5927963:ℝ)/42188800 by norm_num]
    exact paid_terminal_194
  · change terminalPayment 195 ≤ terminalValue ((point cut hi 1024 195+point cut hi 1024 196)/2)
    have hp : terminalPayment 195 = (590350123486:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 195+point cut hi 1024 196)/2 = (174708313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174708313:ℝ)/42188800) = (2521023:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174708313:ℝ)/42188800)-4 = (5953113:ℝ)/42188800 by norm_num]
    exact paid_terminal_195
  · change terminalPayment 196 ≤ terminalValue ((point cut hi 1024 196+point cut hi 1024 197)/2)
    have hp : terminalPayment 196 = (589917430979:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 196+point cut hi 1024 197)/2 = (174733463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174733463:ℝ)/42188800) = (2520017:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174733463:ℝ)/42188800)-4 = (5978263:ℝ)/42188800 by norm_num]
    exact paid_terminal_196
  · change terminalPayment 197 ≤ terminalValue ((point cut hi 1024 197+point cut hi 1024 198)/2)
    have hp : terminalPayment 197 = (589484251626:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 197+point cut hi 1024 198)/2 = (174758613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174758613:ℝ)/42188800) = (2519011:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174758613:ℝ)/42188800)-4 = (6003413:ℝ)/42188800 by norm_num]
    exact paid_terminal_197
  · change terminalPayment 198 ≤ terminalValue ((point cut hi 1024 198+point cut hi 1024 199)/2)
    have hp : terminalPayment 198 = (589050584958:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 198+point cut hi 1024 199)/2 = (174783763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174783763:ℝ)/42188800) = (2518005:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174783763:ℝ)/42188800)-4 = (6028563:ℝ)/42188800 by norm_num]
    exact paid_terminal_198
  · change terminalPayment 199 ≤ terminalValue ((point cut hi 1024 199+point cut hi 1024 200)/2)
    have hp : terminalPayment 199 = (588616430505:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 199+point cut hi 1024 200)/2 = (174808913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174808913:ℝ)/42188800) = (2516999:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174808913:ℝ)/42188800)-4 = (6053713:ℝ)/42188800 by norm_num]
    exact paid_terminal_199
  · change terminalPayment 200 ≤ terminalValue ((point cut hi 1024 200+point cut hi 1024 201)/2)
    have hp : terminalPayment 200 = (588181787795:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 200+point cut hi 1024 201)/2 = (174834063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174834063:ℝ)/42188800) = (2515993:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174834063:ℝ)/42188800)-4 = (6078863:ℝ)/42188800 by norm_num]
    exact paid_terminal_200
  · change terminalPayment 201 ≤ terminalValue ((point cut hi 1024 201+point cut hi 1024 202)/2)
    have hp : terminalPayment 201 = (587746656358:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 201+point cut hi 1024 202)/2 = (174859213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174859213:ℝ)/42188800) = (2514987:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174859213:ℝ)/42188800)-4 = (6104013:ℝ)/42188800 by norm_num]
    exact paid_terminal_201
  · change terminalPayment 202 ≤ terminalValue ((point cut hi 1024 202+point cut hi 1024 203)/2)
    have hp : terminalPayment 202 = (587311035720:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 202+point cut hi 1024 203)/2 = (174884363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174884363:ℝ)/42188800) = (2513981:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174884363:ℝ)/42188800)-4 = (6129163:ℝ)/42188800 by norm_num]
    exact paid_terminal_202
  · change terminalPayment 203 ≤ terminalValue ((point cut hi 1024 203+point cut hi 1024 204)/2)
    have hp : terminalPayment 203 = (586874925408:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 203+point cut hi 1024 204)/2 = (174909513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174909513:ℝ)/42188800) = (2512975:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174909513:ℝ)/42188800)-4 = (6154313:ℝ)/42188800 by norm_num]
    exact paid_terminal_203
  · change terminalPayment 204 ≤ terminalValue ((point cut hi 1024 204+point cut hi 1024 205)/2)
    have hp : terminalPayment 204 = (586438324949:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 204+point cut hi 1024 205)/2 = (174934663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174934663:ℝ)/42188800) = (2511969:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174934663:ℝ)/42188800)-4 = (6179463:ℝ)/42188800 by norm_num]
    exact paid_terminal_204
  · change terminalPayment 205 ≤ terminalValue ((point cut hi 1024 205+point cut hi 1024 206)/2)
    have hp : terminalPayment 205 = (586001233867:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 205+point cut hi 1024 206)/2 = (174959813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174959813:ℝ)/42188800) = (2510963:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174959813:ℝ)/42188800)-4 = (6204613:ℝ)/42188800 by norm_num]
    exact paid_terminal_205
  · change terminalPayment 206 ≤ terminalValue ((point cut hi 1024 206+point cut hi 1024 207)/2)
    have hp : terminalPayment 206 = (585563651687:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 206+point cut hi 1024 207)/2 = (174984963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174984963:ℝ)/42188800) = (2509957:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174984963:ℝ)/42188800)-4 = (6229763:ℝ)/42188800 by norm_num]
    exact paid_terminal_206
  · change terminalPayment 207 ≤ terminalValue ((point cut hi 1024 207+point cut hi 1024 208)/2)
    have hp : terminalPayment 207 = (585125577933:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 207+point cut hi 1024 208)/2 = (175010113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175010113:ℝ)/42188800) = (2508951:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175010113:ℝ)/42188800)-4 = (6254913:ℝ)/42188800 by norm_num]
    exact paid_terminal_207
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_012
