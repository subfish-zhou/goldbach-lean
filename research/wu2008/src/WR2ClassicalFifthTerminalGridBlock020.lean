import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints020
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_020 (j : Fin 16) : terminalPayment (16*20+j.val) ≤
    terminalValue ((point cut hi 1024 (16*20+j.val)+point cut hi 1024 (16*20+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 320 ≤ terminalValue ((point cut hi 1024 320+point cut hi 1024 321)/2)
    have hp : terminalPayment 320 = (532333417215:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 320+point cut hi 1024 321)/2 = (177852063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177852063:ℝ)/42188800) = (2395273:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177852063:ℝ)/42188800)-4 = (9096863:ℝ)/42188800 by norm_num]
    exact paid_terminal_320
  · change terminalPayment 321 ≤ terminalValue ((point cut hi 1024 321+point cut hi 1024 322)/2)
    have hp : terminalPayment 321 = (531835968173:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 321+point cut hi 1024 322)/2 = (177877213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177877213:ℝ)/42188800) = (2394267:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177877213:ℝ)/42188800)-4 = (9122013:ℝ)/42188800 by norm_num]
    exact paid_terminal_321
  · change terminalPayment 322 ≤ terminalValue ((point cut hi 1024 322+point cut hi 1024 323)/2)
    have hp : terminalPayment 322 = (531337967087:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 322+point cut hi 1024 323)/2 = (177902363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177902363:ℝ)/42188800) = (2393261:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177902363:ℝ)/42188800)-4 = (9147163:ℝ)/42188800 by norm_num]
    exact paid_terminal_322
  · change terminalPayment 323 ≤ terminalValue ((point cut hi 1024 323+point cut hi 1024 324)/2)
    have hp : terminalPayment 323 = (530839413379:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 323+point cut hi 1024 324)/2 = (177927513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177927513:ℝ)/42188800) = (2392255:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177927513:ℝ)/42188800)-4 = (9172313:ℝ)/42188800 by norm_num]
    exact paid_terminal_323
  · change terminalPayment 324 ≤ terminalValue ((point cut hi 1024 324+point cut hi 1024 325)/2)
    have hp : terminalPayment 324 = (530340306470:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 324+point cut hi 1024 325)/2 = (177952663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177952663:ℝ)/42188800) = (2391249:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177952663:ℝ)/42188800)-4 = (9197463:ℝ)/42188800 by norm_num]
    exact paid_terminal_324
  · change terminalPayment 325 ≤ terminalValue ((point cut hi 1024 325+point cut hi 1024 326)/2)
    have hp : terminalPayment 325 = (529840645780:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 325+point cut hi 1024 326)/2 = (177977813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177977813:ℝ)/42188800) = (2390243:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177977813:ℝ)/42188800)-4 = (9222613:ℝ)/42188800 by norm_num]
    exact paid_terminal_325
  · change terminalPayment 326 ≤ terminalValue ((point cut hi 1024 326+point cut hi 1024 327)/2)
    have hp : terminalPayment 326 = (529340430728:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 326+point cut hi 1024 327)/2 = (178002963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178002963:ℝ)/42188800) = (2389237:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178002963:ℝ)/42188800)-4 = (9247763:ℝ)/42188800 by norm_num]
    exact paid_terminal_326
  · change terminalPayment 327 ≤ terminalValue ((point cut hi 1024 327+point cut hi 1024 328)/2)
    have hp : terminalPayment 327 = (528839660731:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 327+point cut hi 1024 328)/2 = (178028113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178028113:ℝ)/42188800) = (2388231:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178028113:ℝ)/42188800)-4 = (9272913:ℝ)/42188800 by norm_num]
    exact paid_terminal_327
  · change terminalPayment 328 ≤ terminalValue ((point cut hi 1024 328+point cut hi 1024 329)/2)
    have hp : terminalPayment 328 = (528338335208:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 328+point cut hi 1024 329)/2 = (178053263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178053263:ℝ)/42188800) = (2387225:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178053263:ℝ)/42188800)-4 = (9298063:ℝ)/42188800 by norm_num]
    exact paid_terminal_328
  · change terminalPayment 329 ≤ terminalValue ((point cut hi 1024 329+point cut hi 1024 330)/2)
    have hp : terminalPayment 329 = (527836453574:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 329+point cut hi 1024 330)/2 = (178078413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178078413:ℝ)/42188800) = (2386219:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178078413:ℝ)/42188800)-4 = (9323213:ℝ)/42188800 by norm_num]
    exact paid_terminal_329
  · change terminalPayment 330 ≤ terminalValue ((point cut hi 1024 330+point cut hi 1024 331)/2)
    have hp : terminalPayment 330 = (527334015244:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 330+point cut hi 1024 331)/2 = (178103563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178103563:ℝ)/42188800) = (2385213:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178103563:ℝ)/42188800)-4 = (9348363:ℝ)/42188800 by norm_num]
    exact paid_terminal_330
  · change terminalPayment 331 ≤ terminalValue ((point cut hi 1024 331+point cut hi 1024 332)/2)
    have hp : terminalPayment 331 = (526831019632:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 331+point cut hi 1024 332)/2 = (178128713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178128713:ℝ)/42188800) = (2384207:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178128713:ℝ)/42188800)-4 = (9373513:ℝ)/42188800 by norm_num]
    exact paid_terminal_331
  · change terminalPayment 332 ≤ terminalValue ((point cut hi 1024 332+point cut hi 1024 333)/2)
    have hp : terminalPayment 332 = (526327466152:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 332+point cut hi 1024 333)/2 = (178153863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178153863:ℝ)/42188800) = (2383201:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178153863:ℝ)/42188800)-4 = (9398663:ℝ)/42188800 by norm_num]
    exact paid_terminal_332
  · change terminalPayment 333 ≤ terminalValue ((point cut hi 1024 333+point cut hi 1024 334)/2)
    have hp : terminalPayment 333 = (525823354216:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 333+point cut hi 1024 334)/2 = (178179013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178179013:ℝ)/42188800) = (2382195:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178179013:ℝ)/42188800)-4 = (9423813:ℝ)/42188800 by norm_num]
    exact paid_terminal_333
  · change terminalPayment 334 ≤ terminalValue ((point cut hi 1024 334+point cut hi 1024 335)/2)
    have hp : terminalPayment 334 = (525318683235:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 334+point cut hi 1024 335)/2 = (178204163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178204163:ℝ)/42188800) = (2381189:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178204163:ℝ)/42188800)-4 = (9448963:ℝ)/42188800 by norm_num]
    exact paid_terminal_334
  · change terminalPayment 335 ≤ terminalValue ((point cut hi 1024 335+point cut hi 1024 336)/2)
    have hp : terminalPayment 335 = (524813452619:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 335+point cut hi 1024 336)/2 = (178229313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178229313:ℝ)/42188800) = (2380183:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178229313:ℝ)/42188800)-4 = (9474113:ℝ)/42188800 by norm_num]
    exact paid_terminal_335
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_020
