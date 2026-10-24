import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints011
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_011 (j : Fin 16) : terminalPayment (16*11+j.val) ≤
    terminalValue ((point cut hi 1024 (16*11+j.val)+point cut hi 1024 (16*11+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 176 ≤ terminalValue ((point cut hi 1024 176+point cut hi 1024 177)/2)
    have hp : terminalPayment 176 = (598479398723:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 176+point cut hi 1024 177)/2 = (174230463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174230463:ℝ)/42188800) = (2540137:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174230463:ℝ)/42188800)-4 = (5475263:ℝ)/42188800 by norm_num]
    exact paid_terminal_176
  · change terminalPayment 177 ≤ terminalValue ((point cut hi 1024 177+point cut hi 1024 178)/2)
    have hp : terminalPayment 177 = (598055868178:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 177+point cut hi 1024 178)/2 = (174255613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174255613:ℝ)/42188800) = (2539131:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174255613:ℝ)/42188800)-4 = (5500413:ℝ)/42188800 by norm_num]
    exact paid_terminal_177
  · change terminalPayment 178 ≤ terminalValue ((point cut hi 1024 178+point cut hi 1024 179)/2)
    have hp : terminalPayment 178 = (597631859553:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 178+point cut hi 1024 179)/2 = (174280763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174280763:ℝ)/42188800) = (2538125:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174280763:ℝ)/42188800)-4 = (5525563:ℝ)/42188800 by norm_num]
    exact paid_terminal_178
  · change terminalPayment 179 ≤ terminalValue ((point cut hi 1024 179+point cut hi 1024 180)/2)
    have hp : terminalPayment 179 = (597207372395:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 179+point cut hi 1024 180)/2 = (174305913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174305913:ℝ)/42188800) = (2537119:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174305913:ℝ)/42188800)-4 = (5550713:ℝ)/42188800 by norm_num]
    exact paid_terminal_179
  · change terminalPayment 180 ≤ terminalValue ((point cut hi 1024 180+point cut hi 1024 181)/2)
    have hp : terminalPayment 180 = (596782406248:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 180+point cut hi 1024 181)/2 = (174331063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174331063:ℝ)/42188800) = (2536113:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174331063:ℝ)/42188800)-4 = (5575863:ℝ)/42188800 by norm_num]
    exact paid_terminal_180
  · change terminalPayment 181 ≤ terminalValue ((point cut hi 1024 181+point cut hi 1024 182)/2)
    have hp : terminalPayment 181 = (596356960656:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 181+point cut hi 1024 182)/2 = (174356213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174356213:ℝ)/42188800) = (2535107:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174356213:ℝ)/42188800)-4 = (5601013:ℝ)/42188800 by norm_num]
    exact paid_terminal_181
  · change terminalPayment 182 ≤ terminalValue ((point cut hi 1024 182+point cut hi 1024 183)/2)
    have hp : terminalPayment 182 = (595931035162:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 182+point cut hi 1024 183)/2 = (174381363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174381363:ℝ)/42188800) = (2534101:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174381363:ℝ)/42188800)-4 = (5626163:ℝ)/42188800 by norm_num]
    exact paid_terminal_182
  · change terminalPayment 183 ≤ terminalValue ((point cut hi 1024 183+point cut hi 1024 184)/2)
    have hp : terminalPayment 183 = (595504629310:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 183+point cut hi 1024 184)/2 = (174406513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174406513:ℝ)/42188800) = (2533095:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174406513:ℝ)/42188800)-4 = (5651313:ℝ)/42188800 by norm_num]
    exact paid_terminal_183
  · change terminalPayment 184 ≤ terminalValue ((point cut hi 1024 184+point cut hi 1024 185)/2)
    have hp : terminalPayment 184 = (595077742640:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 184+point cut hi 1024 185)/2 = (174431663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174431663:ℝ)/42188800) = (2532089:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174431663:ℝ)/42188800)-4 = (5676463:ℝ)/42188800 by norm_num]
    exact paid_terminal_184
  · change terminalPayment 185 ≤ terminalValue ((point cut hi 1024 185+point cut hi 1024 186)/2)
    have hp : terminalPayment 185 = (594650374694:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 185+point cut hi 1024 186)/2 = (174456813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174456813:ℝ)/42188800) = (2531083:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174456813:ℝ)/42188800)-4 = (5701613:ℝ)/42188800 by norm_num]
    exact paid_terminal_185
  · change terminalPayment 186 ≤ terminalValue ((point cut hi 1024 186+point cut hi 1024 187)/2)
    have hp : terminalPayment 186 = (594222525012:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 186+point cut hi 1024 187)/2 = (174481963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174481963:ℝ)/42188800) = (2530077:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174481963:ℝ)/42188800)-4 = (5726763:ℝ)/42188800 by norm_num]
    exact paid_terminal_186
  · change terminalPayment 187 ≤ terminalValue ((point cut hi 1024 187+point cut hi 1024 188)/2)
    have hp : terminalPayment 187 = (593794193133:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 187+point cut hi 1024 188)/2 = (174507113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174507113:ℝ)/42188800) = (2529071:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174507113:ℝ)/42188800)-4 = (5751913:ℝ)/42188800 by norm_num]
    exact paid_terminal_187
  · change terminalPayment 188 ≤ terminalValue ((point cut hi 1024 188+point cut hi 1024 189)/2)
    have hp : terminalPayment 188 = (593365378596:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 188+point cut hi 1024 189)/2 = (174532263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174532263:ℝ)/42188800) = (2528065:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174532263:ℝ)/42188800)-4 = (5777063:ℝ)/42188800 by norm_num]
    exact paid_terminal_188
  · change terminalPayment 189 ≤ terminalValue ((point cut hi 1024 189+point cut hi 1024 190)/2)
    have hp : terminalPayment 189 = (592936080938:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 189+point cut hi 1024 190)/2 = (174557413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174557413:ℝ)/42188800) = (2527059:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174557413:ℝ)/42188800)-4 = (5802213:ℝ)/42188800 by norm_num]
    exact paid_terminal_189
  · change terminalPayment 190 ≤ terminalValue ((point cut hi 1024 190+point cut hi 1024 191)/2)
    have hp : terminalPayment 190 = (592506299697:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 190+point cut hi 1024 191)/2 = (174582563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174582563:ℝ)/42188800) = (2526053:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174582563:ℝ)/42188800)-4 = (5827363:ℝ)/42188800 by norm_num]
    exact paid_terminal_190
  · change terminalPayment 191 ≤ terminalValue ((point cut hi 1024 191+point cut hi 1024 192)/2)
    have hp : terminalPayment 191 = (592076034409:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 191+point cut hi 1024 192)/2 = (174607713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174607713:ℝ)/42188800) = (2525047:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174607713:ℝ)/42188800)-4 = (5852513:ℝ)/42188800 by norm_num]
    exact paid_terminal_191
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_011
