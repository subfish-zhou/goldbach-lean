import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints010
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_010 (j : Fin 16) : terminalPayment (16*10+j.val) ≤
    terminalValue ((point cut hi 1024 (16*10+j.val)+point cut hi 1024 (16*10+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 160 ≤ terminalValue ((point cut hi 1024 160+point cut hi 1024 161)/2)
    have hp : terminalPayment 160 = (605191236450:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 160+point cut hi 1024 161)/2 = (173828063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173828063:ℝ)/42188800) = (2556233:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173828063:ℝ)/42188800)-4 = (5072863:ℝ)/42188800 by norm_num]
    exact paid_terminal_160
  · change terminalPayment 161 ≤ terminalValue ((point cut hi 1024 161+point cut hi 1024 162)/2)
    have hp : terminalPayment 161 = (604775294005:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 161+point cut hi 1024 162)/2 = (173853213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173853213:ℝ)/42188800) = (2555227:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173853213:ℝ)/42188800)-4 = (5098013:ℝ)/42188800 by norm_num]
    exact paid_terminal_161
  · change terminalPayment 162 ≤ terminalValue ((point cut hi 1024 162+point cut hi 1024 163)/2)
    have hp : terminalPayment 162 = (604358880647:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 162+point cut hi 1024 163)/2 = (173878363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173878363:ℝ)/42188800) = (2554221:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173878363:ℝ)/42188800)-4 = (5123163:ℝ)/42188800 by norm_num]
    exact paid_terminal_162
  · change terminalPayment 163 ≤ terminalValue ((point cut hi 1024 163+point cut hi 1024 164)/2)
    have hp : terminalPayment 163 = (603941995933:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 163+point cut hi 1024 164)/2 = (173903513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173903513:ℝ)/42188800) = (2553215:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173903513:ℝ)/42188800)-4 = (5148313:ℝ)/42188800 by norm_num]
    exact paid_terminal_163
  · change terminalPayment 164 ≤ terminalValue ((point cut hi 1024 164+point cut hi 1024 165)/2)
    have hp : terminalPayment 164 = (603524639421:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 164+point cut hi 1024 165)/2 = (173928663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173928663:ℝ)/42188800) = (2552209:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173928663:ℝ)/42188800)-4 = (5173463:ℝ)/42188800 by norm_num]
    exact paid_terminal_164
  · change terminalPayment 165 ≤ terminalValue ((point cut hi 1024 165+point cut hi 1024 166)/2)
    have hp : terminalPayment 165 = (603106810666:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 165+point cut hi 1024 166)/2 = (173953813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173953813:ℝ)/42188800) = (2551203:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173953813:ℝ)/42188800)-4 = (5198613:ℝ)/42188800 by norm_num]
    exact paid_terminal_165
  · change terminalPayment 166 ≤ terminalValue ((point cut hi 1024 166+point cut hi 1024 167)/2)
    have hp : terminalPayment 166 = (602688509224:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 166+point cut hi 1024 167)/2 = (173978963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173978963:ℝ)/42188800) = (2550197:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173978963:ℝ)/42188800)-4 = (5223763:ℝ)/42188800 by norm_num]
    exact paid_terminal_166
  · change terminalPayment 167 ≤ terminalValue ((point cut hi 1024 167+point cut hi 1024 168)/2)
    have hp : terminalPayment 167 = (602269734651:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 167+point cut hi 1024 168)/2 = (174004113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174004113:ℝ)/42188800) = (2549191:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174004113:ℝ)/42188800)-4 = (5248913:ℝ)/42188800 by norm_num]
    exact paid_terminal_167
  · change terminalPayment 168 ≤ terminalValue ((point cut hi 1024 168+point cut hi 1024 169)/2)
    have hp : terminalPayment 168 = (601850486500:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 168+point cut hi 1024 169)/2 = (174029263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174029263:ℝ)/42188800) = (2548185:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174029263:ℝ)/42188800)-4 = (5274063:ℝ)/42188800 by norm_num]
    exact paid_terminal_168
  · change terminalPayment 169 ≤ terminalValue ((point cut hi 1024 169+point cut hi 1024 170)/2)
    have hp : terminalPayment 169 = (601430764324:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 169+point cut hi 1024 170)/2 = (174054413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174054413:ℝ)/42188800) = (2547179:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174054413:ℝ)/42188800)-4 = (5299213:ℝ)/42188800 by norm_num]
    exact paid_terminal_169
  · change terminalPayment 170 ≤ terminalValue ((point cut hi 1024 170+point cut hi 1024 171)/2)
    have hp : terminalPayment 170 = (601010567676:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 170+point cut hi 1024 171)/2 = (174079563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174079563:ℝ)/42188800) = (2546173:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174079563:ℝ)/42188800)-4 = (5324363:ℝ)/42188800 by norm_num]
    exact paid_terminal_170
  · change terminalPayment 171 ≤ terminalValue ((point cut hi 1024 171+point cut hi 1024 172)/2)
    have hp : terminalPayment 171 = (600589896108:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 171+point cut hi 1024 172)/2 = (174104713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174104713:ℝ)/42188800) = (2545167:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174104713:ℝ)/42188800)-4 = (5349513:ℝ)/42188800 by norm_num]
    exact paid_terminal_171
  · change terminalPayment 172 ≤ terminalValue ((point cut hi 1024 172+point cut hi 1024 173)/2)
    have hp : terminalPayment 172 = (600168749171:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 172+point cut hi 1024 173)/2 = (174129863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174129863:ℝ)/42188800) = (2544161:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174129863:ℝ)/42188800)-4 = (5374663:ℝ)/42188800 by norm_num]
    exact paid_terminal_172
  · change terminalPayment 173 ≤ terminalValue ((point cut hi 1024 173+point cut hi 1024 174)/2)
    have hp : terminalPayment 173 = (599747126415:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 173+point cut hi 1024 174)/2 = (174155013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174155013:ℝ)/42188800) = (2543155:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174155013:ℝ)/42188800)-4 = (5399813:ℝ)/42188800 by norm_num]
    exact paid_terminal_173
  · change terminalPayment 174 ≤ terminalValue ((point cut hi 1024 174+point cut hi 1024 175)/2)
    have hp : terminalPayment 174 = (599325027389:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 174+point cut hi 1024 175)/2 = (174180163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174180163:ℝ)/42188800) = (2542149:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174180163:ℝ)/42188800)-4 = (5424963:ℝ)/42188800 by norm_num]
    exact paid_terminal_174
  · change terminalPayment 175 ≤ terminalValue ((point cut hi 1024 175+point cut hi 1024 176)/2)
    have hp : terminalPayment 175 = (598902451642:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 175+point cut hi 1024 176)/2 = (174205313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((174205313:ℝ)/42188800) = (2541143:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((174205313:ℝ)/42188800)-4 = (5450113:ℝ)/42188800 by norm_num]
    exact paid_terminal_175
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_010
