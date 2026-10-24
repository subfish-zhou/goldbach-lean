import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints016
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_016 (j : Fin 16) : terminalPayment (16*16+j.val) ≤
    terminalValue ((point cut hi 1024 (16*16+j.val)+point cut hi 1024 (16*16+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 256 ≤ terminalValue ((point cut hi 1024 256+point cut hi 1024 257)/2)
    have hp : terminalPayment 256 = (563047641727:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 256+point cut hi 1024 257)/2 = (176242463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176242463:ℝ)/42188800) = (2459657:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176242463:ℝ)/42188800)-4 = (7487263:ℝ)/42188800 by norm_num]
    exact paid_terminal_256
  · change terminalPayment 257 ≤ terminalValue ((point cut hi 1024 257+point cut hi 1024 258)/2)
    have hp : terminalPayment 257 = (562584363647:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 257+point cut hi 1024 258)/2 = (176267613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176267613:ℝ)/42188800) = (2458651:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176267613:ℝ)/42188800)-4 = (7512413:ℝ)/42188800 by norm_num]
    exact paid_terminal_257
  · change terminalPayment 258 ≤ terminalValue ((point cut hi 1024 258+point cut hi 1024 259)/2)
    have hp : terminalPayment 258 = (562120568600:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 258+point cut hi 1024 259)/2 = (176292763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176292763:ℝ)/42188800) = (2457645:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176292763:ℝ)/42188800)-4 = (7537563:ℝ)/42188800 by norm_num]
    exact paid_terminal_258
  · change terminalPayment 259 ≤ terminalValue ((point cut hi 1024 259+point cut hi 1024 260)/2)
    have hp : terminalPayment 259 = (561656256065:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 259+point cut hi 1024 260)/2 = (176317913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176317913:ℝ)/42188800) = (2456639:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176317913:ℝ)/42188800)-4 = (7562713:ℝ)/42188800 by norm_num]
    exact paid_terminal_259
  · change terminalPayment 260 ≤ terminalValue ((point cut hi 1024 260+point cut hi 1024 261)/2)
    have hp : terminalPayment 260 = (561191425523:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 260+point cut hi 1024 261)/2 = (176343063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176343063:ℝ)/42188800) = (2455633:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176343063:ℝ)/42188800)-4 = (7587863:ℝ)/42188800 by norm_num]
    exact paid_terminal_260
  · change terminalPayment 261 ≤ terminalValue ((point cut hi 1024 261+point cut hi 1024 262)/2)
    have hp : terminalPayment 261 = (560726076451:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 261+point cut hi 1024 262)/2 = (176368213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176368213:ℝ)/42188800) = (2454627:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176368213:ℝ)/42188800)-4 = (7613013:ℝ)/42188800 by norm_num]
    exact paid_terminal_261
  · change terminalPayment 262 ≤ terminalValue ((point cut hi 1024 262+point cut hi 1024 263)/2)
    have hp : terminalPayment 262 = (560260208327:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 262+point cut hi 1024 263)/2 = (176393363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176393363:ℝ)/42188800) = (2453621:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176393363:ℝ)/42188800)-4 = (7638163:ℝ)/42188800 by norm_num]
    exact paid_terminal_262
  · change terminalPayment 263 ≤ terminalValue ((point cut hi 1024 263+point cut hi 1024 264)/2)
    have hp : terminalPayment 263 = (559793820628:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 263+point cut hi 1024 264)/2 = (176418513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176418513:ℝ)/42188800) = (2452615:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176418513:ℝ)/42188800)-4 = (7663313:ℝ)/42188800 by norm_num]
    exact paid_terminal_263
  · change terminalPayment 264 ≤ terminalValue ((point cut hi 1024 264+point cut hi 1024 265)/2)
    have hp : terminalPayment 264 = (559326912829:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 264+point cut hi 1024 265)/2 = (176443663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176443663:ℝ)/42188800) = (2451609:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176443663:ℝ)/42188800)-4 = (7688463:ℝ)/42188800 by norm_num]
    exact paid_terminal_264
  · change terminalPayment 265 ≤ terminalValue ((point cut hi 1024 265+point cut hi 1024 266)/2)
    have hp : terminalPayment 265 = (558859484406:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 265+point cut hi 1024 266)/2 = (176468813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176468813:ℝ)/42188800) = (2450603:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176468813:ℝ)/42188800)-4 = (7713613:ℝ)/42188800 by norm_num]
    exact paid_terminal_265
  · change terminalPayment 266 ≤ terminalValue ((point cut hi 1024 266+point cut hi 1024 267)/2)
    have hp : terminalPayment 266 = (558391534832:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 266+point cut hi 1024 267)/2 = (176493963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176493963:ℝ)/42188800) = (2449597:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176493963:ℝ)/42188800)-4 = (7738763:ℝ)/42188800 by norm_num]
    exact paid_terminal_266
  · change terminalPayment 267 ≤ terminalValue ((point cut hi 1024 267+point cut hi 1024 268)/2)
    have hp : terminalPayment 267 = (557923063580:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 267+point cut hi 1024 268)/2 = (176519113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176519113:ℝ)/42188800) = (2448591:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176519113:ℝ)/42188800)-4 = (7763913:ℝ)/42188800 by norm_num]
    exact paid_terminal_267
  · change terminalPayment 268 ≤ terminalValue ((point cut hi 1024 268+point cut hi 1024 269)/2)
    have hp : terminalPayment 268 = (557454070124:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 268+point cut hi 1024 269)/2 = (176544263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176544263:ℝ)/42188800) = (2447585:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176544263:ℝ)/42188800)-4 = (7789063:ℝ)/42188800 by norm_num]
    exact paid_terminal_268
  · change terminalPayment 269 ≤ terminalValue ((point cut hi 1024 269+point cut hi 1024 270)/2)
    have hp : terminalPayment 269 = (556984553933:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 269+point cut hi 1024 270)/2 = (176569413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176569413:ℝ)/42188800) = (2446579:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176569413:ℝ)/42188800)-4 = (7814213:ℝ)/42188800 by norm_num]
    exact paid_terminal_269
  · change terminalPayment 270 ≤ terminalValue ((point cut hi 1024 270+point cut hi 1024 271)/2)
    have hp : terminalPayment 270 = (556514514479:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 270+point cut hi 1024 271)/2 = (176594563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176594563:ℝ)/42188800) = (2445573:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176594563:ℝ)/42188800)-4 = (7839363:ℝ)/42188800 by norm_num]
    exact paid_terminal_270
  · change terminalPayment 271 ≤ terminalValue ((point cut hi 1024 271+point cut hi 1024 272)/2)
    have hp : terminalPayment 271 = (556043951232:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 271+point cut hi 1024 272)/2 = (176619713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176619713:ℝ)/42188800) = (2444567:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176619713:ℝ)/42188800)-4 = (7864513:ℝ)/42188800 by norm_num]
    exact paid_terminal_271
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_016
