import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints024
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_024 (j : Fin 16) : terminalPayment (16*24+j.val) ≤
    terminalValue ((point cut hi 1024 (16*24+j.val)+point cut hi 1024 (16*24+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 384 ≤ terminalValue ((point cut hi 1024 384+point cut hi 1024 385)/2)
    have hp : terminalPayment 384 = (499359051668:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 384+point cut hi 1024 385)/2 = (179461663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179461663:ℝ)/42188800) = (2330889:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179461663:ℝ)/42188800)-4 = (10706463:ℝ)/42188800 by norm_num]
    exact paid_terminal_384
  · change terminalPayment 385 ≤ terminalValue ((point cut hi 1024 385+point cut hi 1024 386)/2)
    have hp : terminalPayment 385 = (498825065489:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 385+point cut hi 1024 386)/2 = (179486813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179486813:ℝ)/42188800) = (2329883:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179486813:ℝ)/42188800)-4 = (10731613:ℝ)/42188800 by norm_num]
    exact paid_terminal_385
  · change terminalPayment 386 ≤ terminalValue ((point cut hi 1024 386+point cut hi 1024 387)/2)
    have hp : terminalPayment 386 = (498290488274:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 386+point cut hi 1024 387)/2 = (179511963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179511963:ℝ)/42188800) = (2328877:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179511963:ℝ)/42188800)-4 = (10756763:ℝ)/42188800 by norm_num]
    exact paid_terminal_386
  · change terminalPayment 387 ≤ terminalValue ((point cut hi 1024 387+point cut hi 1024 388)/2)
    have hp : terminalPayment 387 = (497755319380:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 387+point cut hi 1024 388)/2 = (179537113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179537113:ℝ)/42188800) = (2327871:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179537113:ℝ)/42188800)-4 = (10781913:ℝ)/42188800 by norm_num]
    exact paid_terminal_387
  · change terminalPayment 388 ≤ terminalValue ((point cut hi 1024 388+point cut hi 1024 389)/2)
    have hp : terminalPayment 388 = (497219558163:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 388+point cut hi 1024 389)/2 = (179562263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179562263:ℝ)/42188800) = (2326865:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179562263:ℝ)/42188800)-4 = (10807063:ℝ)/42188800 by norm_num]
    exact paid_terminal_388
  · change terminalPayment 389 ≤ terminalValue ((point cut hi 1024 389+point cut hi 1024 390)/2)
    have hp : terminalPayment 389 = (496683203979:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 389+point cut hi 1024 390)/2 = (179587413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179587413:ℝ)/42188800) = (2325859:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179587413:ℝ)/42188800)-4 = (10832213:ℝ)/42188800 by norm_num]
    exact paid_terminal_389
  · change terminalPayment 390 ≤ terminalValue ((point cut hi 1024 390+point cut hi 1024 391)/2)
    have hp : terminalPayment 390 = (496146256181:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 390+point cut hi 1024 391)/2 = (179612563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179612563:ℝ)/42188800) = (2324853:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179612563:ℝ)/42188800)-4 = (10857363:ℝ)/42188800 by norm_num]
    exact paid_terminal_390
  · change terminalPayment 391 ≤ terminalValue ((point cut hi 1024 391+point cut hi 1024 392)/2)
    have hp : terminalPayment 391 = (495608714124:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 391+point cut hi 1024 392)/2 = (179637713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179637713:ℝ)/42188800) = (2323847:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179637713:ℝ)/42188800)-4 = (10882513:ℝ)/42188800 by norm_num]
    exact paid_terminal_391
  · change terminalPayment 392 ≤ terminalValue ((point cut hi 1024 392+point cut hi 1024 393)/2)
    have hp : terminalPayment 392 = (495070577159:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 392+point cut hi 1024 393)/2 = (179662863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179662863:ℝ)/42188800) = (2322841:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179662863:ℝ)/42188800)-4 = (10907663:ℝ)/42188800 by norm_num]
    exact paid_terminal_392
  · change terminalPayment 393 ≤ terminalValue ((point cut hi 1024 393+point cut hi 1024 394)/2)
    have hp : terminalPayment 393 = (494531844637:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 393+point cut hi 1024 394)/2 = (179688013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179688013:ℝ)/42188800) = (2321835:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179688013:ℝ)/42188800)-4 = (10932813:ℝ)/42188800 by norm_num]
    exact paid_terminal_393
  · change terminalPayment 394 ≤ terminalValue ((point cut hi 1024 394+point cut hi 1024 395)/2)
    have hp : terminalPayment 394 = (493992515908:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 394+point cut hi 1024 395)/2 = (179713163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179713163:ℝ)/42188800) = (2320829:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179713163:ℝ)/42188800)-4 = (10957963:ℝ)/42188800 by norm_num]
    exact paid_terminal_394
  · change terminalPayment 395 ≤ terminalValue ((point cut hi 1024 395+point cut hi 1024 396)/2)
    have hp : terminalPayment 395 = (493452590323:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 395+point cut hi 1024 396)/2 = (179738313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179738313:ℝ)/42188800) = (2319823:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179738313:ℝ)/42188800)-4 = (10983113:ℝ)/42188800 by norm_num]
    exact paid_terminal_395
  · change terminalPayment 396 ≤ terminalValue ((point cut hi 1024 396+point cut hi 1024 397)/2)
    have hp : terminalPayment 396 = (492912067227:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 396+point cut hi 1024 397)/2 = (179763463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179763463:ℝ)/42188800) = (2318817:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179763463:ℝ)/42188800)-4 = (11008263:ℝ)/42188800 by norm_num]
    exact paid_terminal_396
  · change terminalPayment 397 ≤ terminalValue ((point cut hi 1024 397+point cut hi 1024 398)/2)
    have hp : terminalPayment 397 = (492370945968:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 397+point cut hi 1024 398)/2 = (179788613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179788613:ℝ)/42188800) = (2317811:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179788613:ℝ)/42188800)-4 = (11033413:ℝ)/42188800 by norm_num]
    exact paid_terminal_397
  · change terminalPayment 398 ≤ terminalValue ((point cut hi 1024 398+point cut hi 1024 399)/2)
    have hp : terminalPayment 398 = (491829225893:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 398+point cut hi 1024 399)/2 = (179813763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179813763:ℝ)/42188800) = (2316805:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179813763:ℝ)/42188800)-4 = (11058563:ℝ)/42188800 by norm_num]
    exact paid_terminal_398
  · change terminalPayment 399 ≤ terminalValue ((point cut hi 1024 399+point cut hi 1024 400)/2)
    have hp : terminalPayment 399 = (491286906344:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 399+point cut hi 1024 400)/2 = (179838913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179838913:ℝ)/42188800) = (2315799:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179838913:ℝ)/42188800)-4 = (11083713:ℝ)/42188800 by norm_num]
    exact paid_terminal_399
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_024
