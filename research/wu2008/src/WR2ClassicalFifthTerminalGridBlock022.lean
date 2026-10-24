import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints022
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_022 (j : Fin 16) : terminalPayment (16*22+j.val) ≤
    terminalValue ((point cut hi 1024 (16*22+j.val)+point cut hi 1024 (16*22+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 352 ≤ terminalValue ((point cut hi 1024 352+point cut hi 1024 353)/2)
    have hp : terminalPayment 352 = (516138331902:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 352+point cut hi 1024 353)/2 = (178656863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178656863:ℝ)/42188800) = (2363081:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178656863:ℝ)/42188800)-4 = (9901663:ℝ)/42188800 by norm_num]
    exact paid_terminal_352
  · change terminalPayment 353 ≤ terminalValue ((point cut hi 1024 353+point cut hi 1024 354)/2)
    have hp : terminalPayment 353 = (515622925907:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 353+point cut hi 1024 354)/2 = (178682013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178682013:ℝ)/42188800) = (2362075:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178682013:ℝ)/42188800)-4 = (9926813:ℝ)/42188800 by norm_num]
    exact paid_terminal_353
  · change terminalPayment 354 ≤ terminalValue ((point cut hi 1024 354+point cut hi 1024 355)/2)
    have hp : terminalPayment 354 = (515106948886:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 354+point cut hi 1024 355)/2 = (1735021:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((1735021:ℝ)/409600) = (22923:ℝ)/16384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((1735021:ℝ)/409600)-4 = (96621:ℝ)/409600 by norm_num]
    exact paid_terminal_354
  · change terminalPayment 355 ≤ terminalValue ((point cut hi 1024 355+point cut hi 1024 356)/2)
    have hp : terminalPayment 355 = (514590400230:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 355+point cut hi 1024 356)/2 = (178732313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178732313:ℝ)/42188800) = (2360063:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178732313:ℝ)/42188800)-4 = (9977113:ℝ)/42188800 by norm_num]
    exact paid_terminal_355
  · change terminalPayment 356 ≤ terminalValue ((point cut hi 1024 356+point cut hi 1024 357)/2)
    have hp : terminalPayment 356 = (514073279328:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 356+point cut hi 1024 357)/2 = (178757463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178757463:ℝ)/42188800) = (2359057:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178757463:ℝ)/42188800)-4 = (10002263:ℝ)/42188800 by norm_num]
    exact paid_terminal_356
  · change terminalPayment 357 ≤ terminalValue ((point cut hi 1024 357+point cut hi 1024 358)/2)
    have hp : terminalPayment 357 = (513555585568:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 357+point cut hi 1024 358)/2 = (178782613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178782613:ℝ)/42188800) = (2358051:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178782613:ℝ)/42188800)-4 = (10027413:ℝ)/42188800 by norm_num]
    exact paid_terminal_357
  · change terminalPayment 358 ≤ terminalValue ((point cut hi 1024 358+point cut hi 1024 359)/2)
    have hp : terminalPayment 358 = (513037318339:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 358+point cut hi 1024 359)/2 = (178807763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178807763:ℝ)/42188800) = (2357045:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178807763:ℝ)/42188800)-4 = (10052563:ℝ)/42188800 by norm_num]
    exact paid_terminal_358
  · change terminalPayment 359 ≤ terminalValue ((point cut hi 1024 359+point cut hi 1024 360)/2)
    have hp : terminalPayment 359 = (512518477027:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 359+point cut hi 1024 360)/2 = (178832913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178832913:ℝ)/42188800) = (2356039:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178832913:ℝ)/42188800)-4 = (10077713:ℝ)/42188800 by norm_num]
    exact paid_terminal_359
  · change terminalPayment 360 ≤ terminalValue ((point cut hi 1024 360+point cut hi 1024 361)/2)
    have hp : terminalPayment 360 = (511999061016:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 360+point cut hi 1024 361)/2 = (178858063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178858063:ℝ)/42188800) = (2355033:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178858063:ℝ)/42188800)-4 = (10102863:ℝ)/42188800 by norm_num]
    exact paid_terminal_360
  · change terminalPayment 361 ≤ terminalValue ((point cut hi 1024 361+point cut hi 1024 362)/2)
    have hp : terminalPayment 361 = (511479069693:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 361+point cut hi 1024 362)/2 = (178883213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178883213:ℝ)/42188800) = (2354027:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178883213:ℝ)/42188800)-4 = (10128013:ℝ)/42188800 by norm_num]
    exact paid_terminal_361
  · change terminalPayment 362 ≤ terminalValue ((point cut hi 1024 362+point cut hi 1024 363)/2)
    have hp : terminalPayment 362 = (510958502439:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 362+point cut hi 1024 363)/2 = (178908363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178908363:ℝ)/42188800) = (2353021:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178908363:ℝ)/42188800)-4 = (10153163:ℝ)/42188800 by norm_num]
    exact paid_terminal_362
  · change terminalPayment 363 ≤ terminalValue ((point cut hi 1024 363+point cut hi 1024 364)/2)
    have hp : terminalPayment 363 = (510437358637:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 363+point cut hi 1024 364)/2 = (178933513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178933513:ℝ)/42188800) = (2352015:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178933513:ℝ)/42188800)-4 = (10178313:ℝ)/42188800 by norm_num]
    exact paid_terminal_363
  · change terminalPayment 364 ≤ terminalValue ((point cut hi 1024 364+point cut hi 1024 365)/2)
    have hp : terminalPayment 364 = (509915637670:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 364+point cut hi 1024 365)/2 = (178958663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178958663:ℝ)/42188800) = (2351009:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178958663:ℝ)/42188800)-4 = (10203463:ℝ)/42188800 by norm_num]
    exact paid_terminal_364
  · change terminalPayment 365 ≤ terminalValue ((point cut hi 1024 365+point cut hi 1024 366)/2)
    have hp : terminalPayment 365 = (509393338916:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 365+point cut hi 1024 366)/2 = (178983813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178983813:ℝ)/42188800) = (2350003:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178983813:ℝ)/42188800)-4 = (10228613:ℝ)/42188800 by norm_num]
    exact paid_terminal_365
  · change terminalPayment 366 ≤ terminalValue ((point cut hi 1024 366+point cut hi 1024 367)/2)
    have hp : terminalPayment 366 = (508870461756:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 366+point cut hi 1024 367)/2 = (179008963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179008963:ℝ)/42188800) = (2348997:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179008963:ℝ)/42188800)-4 = (10253763:ℝ)/42188800 by norm_num]
    exact paid_terminal_366
  · change terminalPayment 367 ≤ terminalValue ((point cut hi 1024 367+point cut hi 1024 368)/2)
    have hp : terminalPayment 367 = (508347005568:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 367+point cut hi 1024 368)/2 = (179034113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179034113:ℝ)/42188800) = (2347991:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179034113:ℝ)/42188800)-4 = (10278913:ℝ)/42188800 by norm_num]
    exact paid_terminal_367
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_022
