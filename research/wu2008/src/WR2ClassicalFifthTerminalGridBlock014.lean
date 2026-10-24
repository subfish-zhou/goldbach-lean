import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints014
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_014 (j : Fin 16) : terminalPayment (16*14+j.val) ≤
    terminalValue ((point cut hi 1024 (16*14+j.val)+point cut hi 1024 (16*14+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 224 ≤ terminalValue ((point cut hi 1024 224+point cut hi 1024 225)/2)
    have hp : terminalPayment 224 = (577602647566:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 224+point cut hi 1024 225)/2 = (175437663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175437663:ℝ)/42188800) = (2491849:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175437663:ℝ)/42188800)-4 = (6682463:ℝ)/42188800 by norm_num]
    exact paid_terminal_224
  · change terminalPayment 225 ≤ terminalValue ((point cut hi 1024 225+point cut hi 1024 226)/2)
    have hp : terminalPayment 225 = (577155643069:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 225+point cut hi 1024 226)/2 = (175462813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175462813:ℝ)/42188800) = (2490843:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175462813:ℝ)/42188800)-4 = (6707613:ℝ)/42188800 by norm_num]
    exact paid_terminal_225
  · change terminalPayment 226 ≤ terminalValue ((point cut hi 1024 226+point cut hi 1024 227)/2)
    have hp : terminalPayment 226 = (576708137790:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 226+point cut hi 1024 227)/2 = (175487963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175487963:ℝ)/42188800) = (2489837:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175487963:ℝ)/42188800)-4 = (6732763:ℝ)/42188800 by norm_num]
    exact paid_terminal_226
  · change terminalPayment 227 ≤ terminalValue ((point cut hi 1024 227+point cut hi 1024 228)/2)
    have hp : terminalPayment 227 = (576260131236:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 227+point cut hi 1024 228)/2 = (175513113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175513113:ℝ)/42188800) = (2488831:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175513113:ℝ)/42188800)-4 = (6757913:ℝ)/42188800 by norm_num]
    exact paid_terminal_227
  · change terminalPayment 228 ≤ terminalValue ((point cut hi 1024 228+point cut hi 1024 229)/2)
    have hp : terminalPayment 228 = (575811622915:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 228+point cut hi 1024 229)/2 = (175538263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175538263:ℝ)/42188800) = (2487825:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175538263:ℝ)/42188800)-4 = (6783063:ℝ)/42188800 by norm_num]
    exact paid_terminal_228
  · change terminalPayment 229 ≤ terminalValue ((point cut hi 1024 229+point cut hi 1024 230)/2)
    have hp : terminalPayment 229 = (575362612331:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 229+point cut hi 1024 230)/2 = (175563413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175563413:ℝ)/42188800) = (2486819:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175563413:ℝ)/42188800)-4 = (6808213:ℝ)/42188800 by norm_num]
    exact paid_terminal_229
  · change terminalPayment 230 ≤ terminalValue ((point cut hi 1024 230+point cut hi 1024 231)/2)
    have hp : terminalPayment 230 = (574913098989:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 230+point cut hi 1024 231)/2 = (175588563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175588563:ℝ)/42188800) = (2485813:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175588563:ℝ)/42188800)-4 = (6833363:ℝ)/42188800 by norm_num]
    exact paid_terminal_230
  · change terminalPayment 231 ≤ terminalValue ((point cut hi 1024 231+point cut hi 1024 232)/2)
    have hp : terminalPayment 231 = (574463082393:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 231+point cut hi 1024 232)/2 = (175613713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175613713:ℝ)/42188800) = (2484807:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175613713:ℝ)/42188800)-4 = (6858513:ℝ)/42188800 by norm_num]
    exact paid_terminal_231
  · change terminalPayment 232 ≤ terminalValue ((point cut hi 1024 232+point cut hi 1024 233)/2)
    have hp : terminalPayment 232 = (574012562046:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 232+point cut hi 1024 233)/2 = (175638863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175638863:ℝ)/42188800) = (2483801:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175638863:ℝ)/42188800)-4 = (6883663:ℝ)/42188800 by norm_num]
    exact paid_terminal_232
  · change terminalPayment 233 ≤ terminalValue ((point cut hi 1024 233+point cut hi 1024 234)/2)
    have hp : terminalPayment 233 = (573561537451:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 233+point cut hi 1024 234)/2 = (175664013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175664013:ℝ)/42188800) = (2482795:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175664013:ℝ)/42188800)-4 = (6908813:ℝ)/42188800 by norm_num]
    exact paid_terminal_233
  · change terminalPayment 234 ≤ terminalValue ((point cut hi 1024 234+point cut hi 1024 235)/2)
    have hp : terminalPayment 234 = (573110008108:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 234+point cut hi 1024 235)/2 = (175689163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175689163:ℝ)/42188800) = (2481789:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175689163:ℝ)/42188800)-4 = (6933963:ℝ)/42188800 by norm_num]
    exact paid_terminal_234
  · change terminalPayment 235 ≤ terminalValue ((point cut hi 1024 235+point cut hi 1024 236)/2)
    have hp : terminalPayment 235 = (572657973519:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 235+point cut hi 1024 236)/2 = (175714313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175714313:ℝ)/42188800) = (2480783:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175714313:ℝ)/42188800)-4 = (6959113:ℝ)/42188800 by norm_num]
    exact paid_terminal_235
  · change terminalPayment 236 ≤ terminalValue ((point cut hi 1024 236+point cut hi 1024 237)/2)
    have hp : terminalPayment 236 = (572205433183:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 236+point cut hi 1024 237)/2 = (175739463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175739463:ℝ)/42188800) = (2479777:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175739463:ℝ)/42188800)-4 = (6984263:ℝ)/42188800 by norm_num]
    exact paid_terminal_236
  · change terminalPayment 237 ≤ terminalValue ((point cut hi 1024 237+point cut hi 1024 238)/2)
    have hp : terminalPayment 237 = (571752386599:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 237+point cut hi 1024 238)/2 = (175764613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175764613:ℝ)/42188800) = (2478771:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175764613:ℝ)/42188800)-4 = (7009413:ℝ)/42188800 by norm_num]
    exact paid_terminal_237
  · change terminalPayment 238 ≤ terminalValue ((point cut hi 1024 238+point cut hi 1024 239)/2)
    have hp : terminalPayment 238 = (571298833265:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 238+point cut hi 1024 239)/2 = (175789763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175789763:ℝ)/42188800) = (2477765:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175789763:ℝ)/42188800)-4 = (7034563:ℝ)/42188800 by norm_num]
    exact paid_terminal_238
  · change terminalPayment 239 ≤ terminalValue ((point cut hi 1024 239+point cut hi 1024 240)/2)
    have hp : terminalPayment 239 = (570844772678:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 239+point cut hi 1024 240)/2 = (175814913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((175814913:ℝ)/42188800) = (2476759:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((175814913:ℝ)/42188800)-4 = (7059713:ℝ)/42188800 by norm_num]
    exact paid_terminal_239
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_014
