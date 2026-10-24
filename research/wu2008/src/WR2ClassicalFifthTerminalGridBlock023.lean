import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints023
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_023 (j : Fin 16) : terminalPayment (16*23+j.val) ≤
    terminalValue ((point cut hi 1024 (16*23+j.val)+point cut hi 1024 (16*23+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 368 ≤ terminalValue ((point cut hi 1024 368+point cut hi 1024 369)/2)
    have hp : terminalPayment 368 = (507822969729:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 368+point cut hi 1024 369)/2 = (179059263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179059263:ℝ)/42188800) = (2346985:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179059263:ℝ)/42188800)-4 = (10304063:ℝ)/42188800 by norm_num]
    exact paid_terminal_368
  · change terminalPayment 369 ≤ terminalValue ((point cut hi 1024 369+point cut hi 1024 370)/2)
    have hp : terminalPayment 369 = (507298353616:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 369+point cut hi 1024 370)/2 = (179084413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179084413:ℝ)/42188800) = (2345979:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179084413:ℝ)/42188800)-4 = (10329213:ℝ)/42188800 by norm_num]
    exact paid_terminal_369
  · change terminalPayment 370 ≤ terminalValue ((point cut hi 1024 370+point cut hi 1024 371)/2)
    have hp : terminalPayment 370 = (506773156603:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 370+point cut hi 1024 371)/2 = (179109563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179109563:ℝ)/42188800) = (2344973:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179109563:ℝ)/42188800)-4 = (10354363:ℝ)/42188800 by norm_num]
    exact paid_terminal_370
  · change terminalPayment 371 ≤ terminalValue ((point cut hi 1024 371+point cut hi 1024 372)/2)
    have hp : terminalPayment 371 = (506247378065:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 371+point cut hi 1024 372)/2 = (179134713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179134713:ℝ)/42188800) = (2343967:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179134713:ℝ)/42188800)-4 = (10379513:ℝ)/42188800 by norm_num]
    exact paid_terminal_371
  · change terminalPayment 372 ≤ terminalValue ((point cut hi 1024 372+point cut hi 1024 373)/2)
    have hp : terminalPayment 372 = (505721017375:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 372+point cut hi 1024 373)/2 = (179159863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179159863:ℝ)/42188800) = (2342961:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179159863:ℝ)/42188800)-4 = (10404663:ℝ)/42188800 by norm_num]
    exact paid_terminal_372
  · change terminalPayment 373 ≤ terminalValue ((point cut hi 1024 373+point cut hi 1024 374)/2)
    have hp : terminalPayment 373 = (505194073905:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 373+point cut hi 1024 374)/2 = (179185013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179185013:ℝ)/42188800) = (2341955:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179185013:ℝ)/42188800)-4 = (10429813:ℝ)/42188800 by norm_num]
    exact paid_terminal_373
  · change terminalPayment 374 ≤ terminalValue ((point cut hi 1024 374+point cut hi 1024 375)/2)
    have hp : terminalPayment 374 = (504666547027:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 374+point cut hi 1024 375)/2 = (179210163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179210163:ℝ)/42188800) = (2340949:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179210163:ℝ)/42188800)-4 = (10454963:ℝ)/42188800 by norm_num]
    exact paid_terminal_374
  · change terminalPayment 375 ≤ terminalValue ((point cut hi 1024 375+point cut hi 1024 376)/2)
    have hp : terminalPayment 375 = (504138436110:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 375+point cut hi 1024 376)/2 = (179235313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179235313:ℝ)/42188800) = (2339943:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179235313:ℝ)/42188800)-4 = (10480113:ℝ)/42188800 by norm_num]
    exact paid_terminal_375
  · change terminalPayment 376 ≤ terminalValue ((point cut hi 1024 376+point cut hi 1024 377)/2)
    have hp : terminalPayment 376 = (503609740524:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 376+point cut hi 1024 377)/2 = (179260463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179260463:ℝ)/42188800) = (2338937:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179260463:ℝ)/42188800)-4 = (10505263:ℝ)/42188800 by norm_num]
    exact paid_terminal_376
  · change terminalPayment 377 ≤ terminalValue ((point cut hi 1024 377+point cut hi 1024 378)/2)
    have hp : terminalPayment 377 = (503080459635:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 377+point cut hi 1024 378)/2 = (179285613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179285613:ℝ)/42188800) = (2337931:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179285613:ℝ)/42188800)-4 = (10530413:ℝ)/42188800 by norm_num]
    exact paid_terminal_377
  · change terminalPayment 378 ≤ terminalValue ((point cut hi 1024 378+point cut hi 1024 379)/2)
    have hp : terminalPayment 378 = (502550592813:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 378+point cut hi 1024 379)/2 = (179310763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179310763:ℝ)/42188800) = (2336925:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179310763:ℝ)/42188800)-4 = (10555563:ℝ)/42188800 by norm_num]
    exact paid_terminal_378
  · change terminalPayment 379 ≤ terminalValue ((point cut hi 1024 379+point cut hi 1024 380)/2)
    have hp : terminalPayment 379 = (502020139421:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 379+point cut hi 1024 380)/2 = (179335913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179335913:ℝ)/42188800) = (2335919:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179335913:ℝ)/42188800)-4 = (10580713:ℝ)/42188800 by norm_num]
    exact paid_terminal_379
  · change terminalPayment 380 ≤ terminalValue ((point cut hi 1024 380+point cut hi 1024 381)/2)
    have hp : terminalPayment 380 = (501489098826:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 380+point cut hi 1024 381)/2 = (179361063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179361063:ℝ)/42188800) = (2334913:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179361063:ℝ)/42188800)-4 = (10605863:ℝ)/42188800 by norm_num]
    exact paid_terminal_380
  · change terminalPayment 381 ≤ terminalValue ((point cut hi 1024 381+point cut hi 1024 382)/2)
    have hp : terminalPayment 381 = (500957470391:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 381+point cut hi 1024 382)/2 = (179386213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179386213:ℝ)/42188800) = (2333907:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179386213:ℝ)/42188800)-4 = (10631013:ℝ)/42188800 by norm_num]
    exact paid_terminal_381
  · change terminalPayment 382 ≤ terminalValue ((point cut hi 1024 382+point cut hi 1024 383)/2)
    have hp : terminalPayment 382 = (500425253478:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 382+point cut hi 1024 383)/2 = (179411363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179411363:ℝ)/42188800) = (2332901:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179411363:ℝ)/42188800)-4 = (10656163:ℝ)/42188800 by norm_num]
    exact paid_terminal_382
  · change terminalPayment 383 ≤ terminalValue ((point cut hi 1024 383+point cut hi 1024 384)/2)
    have hp : terminalPayment 383 = (499892447450:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 383+point cut hi 1024 384)/2 = (179436513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179436513:ℝ)/42188800) = (2331895:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179436513:ℝ)/42188800)-4 = (10681313:ℝ)/42188800 by norm_num]
    exact paid_terminal_383
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_023
