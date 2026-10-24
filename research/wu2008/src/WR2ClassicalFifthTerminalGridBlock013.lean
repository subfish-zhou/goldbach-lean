import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints013
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_013 (j : Fin 16) : terminalPayment (16*13+j.val) ≤
    terminalValue ((point cut hi 1024 (16*13+j.val)+point cut hi 1024 (16*13+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 208 ≤ terminalValue ((point cut hi 1024 208+point cut hi 1024 209)/2)
    have hp : terminalPayment 208 = (584687012126:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 208+point cut hi 1024 209)/2 = (175035263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175035263:ℝ)/42188800) = (2507945:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175035263:ℝ)/42188800)-4 = (6280063:ℝ)/42188800 by norm_num]
    exact paid_terminal_208
  · change terminalPayment 209 ≤ terminalValue ((point cut hi 1024 209+point cut hi 1024 210)/2)
    have hp : terminalPayment 209 = (584247953789:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 209+point cut hi 1024 210)/2 = (175060413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175060413:ℝ)/42188800) = (2506939:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175060413:ℝ)/42188800)-4 = (6305213:ℝ)/42188800 by norm_num]
    exact paid_terminal_209
  · change terminalPayment 210 ≤ terminalValue ((point cut hi 1024 210+point cut hi 1024 211)/2)
    have hp : terminalPayment 210 = (583808402444:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 210+point cut hi 1024 211)/2 = (175085563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175085563:ℝ)/42188800) = (2505933:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175085563:ℝ)/42188800)-4 = (6330363:ℝ)/42188800 by norm_num]
    exact paid_terminal_210
  · change terminalPayment 211 ≤ terminalValue ((point cut hi 1024 211+point cut hi 1024 212)/2)
    have hp : terminalPayment 211 = (583368357610:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 211+point cut hi 1024 212)/2 = (175110713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175110713:ℝ)/42188800) = (2504927:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175110713:ℝ)/42188800)-4 = (6355513:ℝ)/42188800 by norm_num]
    exact paid_terminal_211
  · change terminalPayment 212 ≤ terminalValue ((point cut hi 1024 212+point cut hi 1024 213)/2)
    have hp : terminalPayment 212 = (582927818807:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 212+point cut hi 1024 213)/2 = (175135863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175135863:ℝ)/42188800) = (2503921:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175135863:ℝ)/42188800)-4 = (6380663:ℝ)/42188800 by norm_num]
    exact paid_terminal_212
  · change terminalPayment 213 ≤ terminalValue ((point cut hi 1024 213+point cut hi 1024 214)/2)
    have hp : terminalPayment 213 = (582486785553:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 213+point cut hi 1024 214)/2 = (175161013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175161013:ℝ)/42188800) = (2502915:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175161013:ℝ)/42188800)-4 = (6405813:ℝ)/42188800 by norm_num]
    exact paid_terminal_213
  · change terminalPayment 214 ≤ terminalValue ((point cut hi 1024 214+point cut hi 1024 215)/2)
    have hp : terminalPayment 214 = (582045257367:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 214+point cut hi 1024 215)/2 = (175186163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175186163:ℝ)/42188800) = (2501909:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175186163:ℝ)/42188800)-4 = (6430963:ℝ)/42188800 by norm_num]
    exact paid_terminal_214
  · change terminalPayment 215 ≤ terminalValue ((point cut hi 1024 215+point cut hi 1024 216)/2)
    have hp : terminalPayment 215 = (581603233765:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 215+point cut hi 1024 216)/2 = (175211313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175211313:ℝ)/42188800) = (2500903:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175211313:ℝ)/42188800)-4 = (6456113:ℝ)/42188800 by norm_num]
    exact paid_terminal_215
  · change terminalPayment 216 ≤ terminalValue ((point cut hi 1024 216+point cut hi 1024 217)/2)
    have hp : terminalPayment 216 = (581160714264:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 216+point cut hi 1024 217)/2 = (175236463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175236463:ℝ)/42188800) = (2499897:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175236463:ℝ)/42188800)-4 = (6481263:ℝ)/42188800 by norm_num]
    exact paid_terminal_216
  · change terminalPayment 217 ≤ terminalValue ((point cut hi 1024 217+point cut hi 1024 218)/2)
    have hp : terminalPayment 217 = (580717698380:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 217+point cut hi 1024 218)/2 = (175261613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175261613:ℝ)/42188800) = (2498891:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175261613:ℝ)/42188800)-4 = (6506413:ℝ)/42188800 by norm_num]
    exact paid_terminal_217
  · change terminalPayment 218 ≤ terminalValue ((point cut hi 1024 218+point cut hi 1024 219)/2)
    have hp : terminalPayment 218 = (580274185626:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 218+point cut hi 1024 219)/2 = (175286763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175286763:ℝ)/42188800) = (2497885:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175286763:ℝ)/42188800)-4 = (6531563:ℝ)/42188800 by norm_num]
    exact paid_terminal_218
  · change terminalPayment 219 ≤ terminalValue ((point cut hi 1024 219+point cut hi 1024 220)/2)
    have hp : terminalPayment 219 = (579830175517:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 219+point cut hi 1024 220)/2 = (175311913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175311913:ℝ)/42188800) = (2496879:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175311913:ℝ)/42188800)-4 = (6556713:ℝ)/42188800 by norm_num]
    exact paid_terminal_219
  · change terminalPayment 220 ≤ terminalValue ((point cut hi 1024 220+point cut hi 1024 221)/2)
    have hp : terminalPayment 220 = (579385667565:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 220+point cut hi 1024 221)/2 = (175337063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175337063:ℝ)/42188800) = (2495873:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175337063:ℝ)/42188800)-4 = (6581863:ℝ)/42188800 by norm_num]
    exact paid_terminal_220
  · change terminalPayment 221 ≤ terminalValue ((point cut hi 1024 221+point cut hi 1024 222)/2)
    have hp : terminalPayment 221 = (578940661283:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 221+point cut hi 1024 222)/2 = (175362213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175362213:ℝ)/42188800) = (2494867:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175362213:ℝ)/42188800)-4 = (6607013:ℝ)/42188800 by norm_num]
    exact paid_terminal_221
  · change terminalPayment 222 ≤ terminalValue ((point cut hi 1024 222+point cut hi 1024 223)/2)
    have hp : terminalPayment 222 = (578495156183:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 222+point cut hi 1024 223)/2 = (175387363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175387363:ℝ)/42188800) = (2493861:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175387363:ℝ)/42188800)-4 = (6632163:ℝ)/42188800 by norm_num]
    exact paid_terminal_222
  · change terminalPayment 223 ≤ terminalValue ((point cut hi 1024 223+point cut hi 1024 224)/2)
    have hp : terminalPayment 223 = (578049151774:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 223+point cut hi 1024 224)/2 = (175412513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175412513:ℝ)/42188800) = (2492855:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175412513:ℝ)/42188800)-4 = (6657313:ℝ)/42188800 by norm_num]
    exact paid_terminal_223
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_013
