import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints018
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_018 (j : Fin 16) : terminalPayment (16*18+j.val) ≤
    terminalValue ((point cut hi 1024 (16*18+j.val)+point cut hi 1024 (16*18+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 288 ≤ terminalValue ((point cut hi 1024 288+point cut hi 1024 289)/2)
    have hp : terminalPayment 288 = (547963717356:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 288+point cut hi 1024 289)/2 = (177047263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177047263:ℝ)/42188800) = (2427465:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177047263:ℝ)/42188800)-4 = (8292063:ℝ)/42188800 by norm_num]
    exact paid_terminal_288
  · change terminalPayment 289 ≤ terminalValue ((point cut hi 1024 289+point cut hi 1024 290)/2)
    have hp : terminalPayment 289 = (547483634115:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 289+point cut hi 1024 290)/2 = (177072413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177072413:ℝ)/42188800) = (2426459:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177072413:ℝ)/42188800)-4 = (8317213:ℝ)/42188800 by norm_num]
    exact paid_terminal_289
  · change terminalPayment 290 ≤ terminalValue ((point cut hi 1024 290+point cut hi 1024 291)/2)
    have hp : terminalPayment 290 = (547003016834:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 290+point cut hi 1024 291)/2 = (177097563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177097563:ℝ)/42188800) = (2425453:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177097563:ℝ)/42188800)-4 = (8342363:ℝ)/42188800 by norm_num]
    exact paid_terminal_290
  · change terminalPayment 291 ≤ terminalValue ((point cut hi 1024 291+point cut hi 1024 292)/2)
    have hp : terminalPayment 291 = (546521864964:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 291+point cut hi 1024 292)/2 = (177122713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177122713:ℝ)/42188800) = (2424447:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177122713:ℝ)/42188800)-4 = (8367513:ℝ)/42188800 by norm_num]
    exact paid_terminal_291
  · change terminalPayment 292 ≤ terminalValue ((point cut hi 1024 292+point cut hi 1024 293)/2)
    have hp : terminalPayment 292 = (546040177957:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 292+point cut hi 1024 293)/2 = (177147863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177147863:ℝ)/42188800) = (2423441:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177147863:ℝ)/42188800)-4 = (8392663:ℝ)/42188800 by norm_num]
    exact paid_terminal_292
  · change terminalPayment 293 ≤ terminalValue ((point cut hi 1024 293+point cut hi 1024 294)/2)
    have hp : terminalPayment 293 = (545557955262:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 293+point cut hi 1024 294)/2 = (177173013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177173013:ℝ)/42188800) = (2422435:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177173013:ℝ)/42188800)-4 = (8417813:ℝ)/42188800 by norm_num]
    exact paid_terminal_293
  · change terminalPayment 294 ≤ terminalValue ((point cut hi 1024 294+point cut hi 1024 295)/2)
    have hp : terminalPayment 294 = (545075196329:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 294+point cut hi 1024 295)/2 = (177198163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177198163:ℝ)/42188800) = (2421429:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177198163:ℝ)/42188800)-4 = (8442963:ℝ)/42188800 by norm_num]
    exact paid_terminal_294
  · change terminalPayment 295 ≤ terminalValue ((point cut hi 1024 295+point cut hi 1024 296)/2)
    have hp : terminalPayment 295 = (544591900604:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 295+point cut hi 1024 296)/2 = (177223313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177223313:ℝ)/42188800) = (2420423:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177223313:ℝ)/42188800)-4 = (8468113:ℝ)/42188800 by norm_num]
    exact paid_terminal_295
  · change terminalPayment 296 ≤ terminalValue ((point cut hi 1024 296+point cut hi 1024 297)/2)
    have hp : terminalPayment 296 = (544108067537:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 296+point cut hi 1024 297)/2 = (177248463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177248463:ℝ)/42188800) = (2419417:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177248463:ℝ)/42188800)-4 = (8493263:ℝ)/42188800 by norm_num]
    exact paid_terminal_296
  · change terminalPayment 297 ≤ terminalValue ((point cut hi 1024 297+point cut hi 1024 298)/2)
    have hp : terminalPayment 297 = (543623696572:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 297+point cut hi 1024 298)/2 = (177273613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177273613:ℝ)/42188800) = (2418411:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177273613:ℝ)/42188800)-4 = (8518413:ℝ)/42188800 by norm_num]
    exact paid_terminal_297
  · change terminalPayment 298 ≤ terminalValue ((point cut hi 1024 298+point cut hi 1024 299)/2)
    have hp : terminalPayment 298 = (543138787154:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 298+point cut hi 1024 299)/2 = (177298763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177298763:ℝ)/42188800) = (2417405:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177298763:ℝ)/42188800)-4 = (8543563:ℝ)/42188800 by norm_num]
    exact paid_terminal_298
  · change terminalPayment 299 ≤ terminalValue ((point cut hi 1024 299+point cut hi 1024 300)/2)
    have hp : terminalPayment 299 = (542653338730:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 299+point cut hi 1024 300)/2 = (177323913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177323913:ℝ)/42188800) = (2416399:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177323913:ℝ)/42188800)-4 = (8568713:ℝ)/42188800 by norm_num]
    exact paid_terminal_299
  · change terminalPayment 300 ≤ terminalValue ((point cut hi 1024 300+point cut hi 1024 301)/2)
    have hp : terminalPayment 300 = (542167350741:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 300+point cut hi 1024 301)/2 = (177349063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177349063:ℝ)/42188800) = (2415393:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177349063:ℝ)/42188800)-4 = (8593863:ℝ)/42188800 by norm_num]
    exact paid_terminal_300
  · change terminalPayment 301 ≤ terminalValue ((point cut hi 1024 301+point cut hi 1024 302)/2)
    have hp : terminalPayment 301 = (541680822631:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 301+point cut hi 1024 302)/2 = (177374213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177374213:ℝ)/42188800) = (2414387:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177374213:ℝ)/42188800)-4 = (8619013:ℝ)/42188800 by norm_num]
    exact paid_terminal_301
  · change terminalPayment 302 ≤ terminalValue ((point cut hi 1024 302+point cut hi 1024 303)/2)
    have hp : terminalPayment 302 = (541193753840:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 302+point cut hi 1024 303)/2 = (177399363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177399363:ℝ)/42188800) = (2413381:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177399363:ℝ)/42188800)-4 = (8644163:ℝ)/42188800 by norm_num]
    exact paid_terminal_302
  · change terminalPayment 303 ≤ terminalValue ((point cut hi 1024 303+point cut hi 1024 304)/2)
    have hp : terminalPayment 303 = (540706143810:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 303+point cut hi 1024 304)/2 = (177424513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177424513:ℝ)/42188800) = (2412375:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177424513:ℝ)/42188800)-4 = (8669313:ℝ)/42188800 by norm_num]
    exact paid_terminal_303
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_018
