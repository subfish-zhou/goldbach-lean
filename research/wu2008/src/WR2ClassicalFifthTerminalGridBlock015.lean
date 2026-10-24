import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints015
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_015 (j : Fin 16) : terminalPayment (16*15+j.val) ≤
    terminalValue ((point cut hi 1024 (16*15+j.val)+point cut hi 1024 (16*15+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 240 ≤ terminalValue ((point cut hi 1024 240+point cut hi 1024 241)/2)
    have hp : terminalPayment 240 = (570390204335:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 240+point cut hi 1024 241)/2 = (175840063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175840063:ℝ)/42188800) = (2475753:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175840063:ℝ)/42188800)-4 = (7084863:ℝ)/42188800 by norm_num]
    exact paid_terminal_240
  · change terminalPayment 241 ≤ terminalValue ((point cut hi 1024 241+point cut hi 1024 242)/2)
    have hp : terminalPayment 241 = (569935127731:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 241+point cut hi 1024 242)/2 = (175865213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175865213:ℝ)/42188800) = (2474747:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175865213:ℝ)/42188800)-4 = (7110013:ℝ)/42188800 by norm_num]
    exact paid_terminal_241
  · change terminalPayment 242 ≤ terminalValue ((point cut hi 1024 242+point cut hi 1024 243)/2)
    have hp : terminalPayment 242 = (569479542361:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 242+point cut hi 1024 243)/2 = (175890363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175890363:ℝ)/42188800) = (2473741:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175890363:ℝ)/42188800)-4 = (7135163:ℝ)/42188800 by norm_num]
    exact paid_terminal_242
  · change terminalPayment 243 ≤ terminalValue ((point cut hi 1024 243+point cut hi 1024 244)/2)
    have hp : terminalPayment 243 = (569023447718:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 243+point cut hi 1024 244)/2 = (175915513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175915513:ℝ)/42188800) = (2472735:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175915513:ℝ)/42188800)-4 = (7160313:ℝ)/42188800 by norm_num]
    exact paid_terminal_243
  · change terminalPayment 244 ≤ terminalValue ((point cut hi 1024 244+point cut hi 1024 245)/2)
    have hp : terminalPayment 244 = (568566843297:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 244+point cut hi 1024 245)/2 = (175940663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175940663:ℝ)/42188800) = (2471729:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175940663:ℝ)/42188800)-4 = (7185463:ℝ)/42188800 by norm_num]
    exact paid_terminal_244
  · change terminalPayment 245 ≤ terminalValue ((point cut hi 1024 245+point cut hi 1024 246)/2)
    have hp : terminalPayment 245 = (568109728587:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 245+point cut hi 1024 246)/2 = (175965813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175965813:ℝ)/42188800) = (2470723:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175965813:ℝ)/42188800)-4 = (7210613:ℝ)/42188800 by norm_num]
    exact paid_terminal_245
  · change terminalPayment 246 ≤ terminalValue ((point cut hi 1024 246+point cut hi 1024 247)/2)
    have hp : terminalPayment 246 = (567652103082:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 246+point cut hi 1024 247)/2 = (175990963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175990963:ℝ)/42188800) = (2469717:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175990963:ℝ)/42188800)-4 = (7235763:ℝ)/42188800 by norm_num]
    exact paid_terminal_246
  · change terminalPayment 247 ≤ terminalValue ((point cut hi 1024 247+point cut hi 1024 248)/2)
    have hp : terminalPayment 247 = (567193966272:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 247+point cut hi 1024 248)/2 = (176016113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176016113:ℝ)/42188800) = (2468711:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176016113:ℝ)/42188800)-4 = (7260913:ℝ)/42188800 by norm_num]
    exact paid_terminal_247
  · change terminalPayment 248 ≤ terminalValue ((point cut hi 1024 248+point cut hi 1024 249)/2)
    have hp : terminalPayment 248 = (566735317645:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 248+point cut hi 1024 249)/2 = (176041263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176041263:ℝ)/42188800) = (2467705:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176041263:ℝ)/42188800)-4 = (7286063:ℝ)/42188800 by norm_num]
    exact paid_terminal_248
  · change terminalPayment 249 ≤ terminalValue ((point cut hi 1024 249+point cut hi 1024 250)/2)
    have hp : terminalPayment 249 = (566276156691:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 249+point cut hi 1024 250)/2 = (176066413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176066413:ℝ)/42188800) = (2466699:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176066413:ℝ)/42188800)-4 = (7311213:ℝ)/42188800 by norm_num]
    exact paid_terminal_249
  · change terminalPayment 250 ≤ terminalValue ((point cut hi 1024 250+point cut hi 1024 251)/2)
    have hp : terminalPayment 250 = (565816482898:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 250+point cut hi 1024 251)/2 = (176091563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176091563:ℝ)/42188800) = (2465693:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176091563:ℝ)/42188800)-4 = (7336363:ℝ)/42188800 by norm_num]
    exact paid_terminal_250
  · change terminalPayment 251 ≤ terminalValue ((point cut hi 1024 251+point cut hi 1024 252)/2)
    have hp : terminalPayment 251 = (565356295753:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 251+point cut hi 1024 252)/2 = (1709871:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((1709871:ℝ)/409600) = (23929:ℝ)/16384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((1709871:ℝ)/409600)-4 = (71471:ℝ)/409600 by norm_num]
    exact paid_terminal_251
  · change terminalPayment 252 ≤ terminalValue ((point cut hi 1024 252+point cut hi 1024 253)/2)
    have hp : terminalPayment 252 = (564895594741:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 252+point cut hi 1024 253)/2 = (176141863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176141863:ℝ)/42188800) = (2463681:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176141863:ℝ)/42188800)-4 = (7386663:ℝ)/42188800 by norm_num]
    exact paid_terminal_252
  · change terminalPayment 253 ≤ terminalValue ((point cut hi 1024 253+point cut hi 1024 254)/2)
    have hp : terminalPayment 253 = (564434379349:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 253+point cut hi 1024 254)/2 = (176167013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176167013:ℝ)/42188800) = (2462675:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176167013:ℝ)/42188800)-4 = (7411813:ℝ)/42188800 by norm_num]
    exact paid_terminal_253
  · change terminalPayment 254 ≤ terminalValue ((point cut hi 1024 254+point cut hi 1024 255)/2)
    have hp : terminalPayment 254 = (563972649060:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 254+point cut hi 1024 255)/2 = (176192163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176192163:ℝ)/42188800) = (2461669:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176192163:ℝ)/42188800)-4 = (7436963:ℝ)/42188800 by norm_num]
    exact paid_terminal_254
  · change terminalPayment 255 ≤ terminalValue ((point cut hi 1024 255+point cut hi 1024 256)/2)
    have hp : terminalPayment 255 = (563510403359:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 255+point cut hi 1024 256)/2 = (176217313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176217313:ℝ)/42188800) = (2460663:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176217313:ℝ)/42188800)-4 = (7462113:ℝ)/42188800 by norm_num]
    exact paid_terminal_255
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_015
