import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints025
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_025 (j : Fin 16) : terminalPayment (16*25+j.val) ≤
    terminalValue ((point cut hi 1024 (16*25+j.val)+point cut hi 1024 (16*25+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 400 ≤ terminalValue ((point cut hi 1024 400+point cut hi 1024 401)/2)
    have hp : terminalPayment 400 = (490743986667:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 400+point cut hi 1024 401)/2 = (179864063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179864063:ℝ)/42188800) = (2314793:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179864063:ℝ)/42188800)-4 = (11108863:ℝ)/42188800 by norm_num]
    exact paid_terminal_400
  · change terminalPayment 401 ≤ terminalValue ((point cut hi 1024 401+point cut hi 1024 402)/2)
    have hp : terminalPayment 401 = (490200466204:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 401+point cut hi 1024 402)/2 = (179889213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179889213:ℝ)/42188800) = (2313787:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179889213:ℝ)/42188800)-4 = (11134013:ℝ)/42188800 by norm_num]
    exact paid_terminal_401
  · change terminalPayment 402 ≤ terminalValue ((point cut hi 1024 402+point cut hi 1024 403)/2)
    have hp : terminalPayment 402 = (489656344295:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 402+point cut hi 1024 403)/2 = (179914363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179914363:ℝ)/42188800) = (2312781:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179914363:ℝ)/42188800)-4 = (11159163:ℝ)/42188800 by norm_num]
    exact paid_terminal_402
  · change terminalPayment 403 ≤ terminalValue ((point cut hi 1024 403+point cut hi 1024 404)/2)
    have hp : terminalPayment 403 = (489111620282:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 403+point cut hi 1024 404)/2 = (179939513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179939513:ℝ)/42188800) = (2311775:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179939513:ℝ)/42188800)-4 = (11184313:ℝ)/42188800 by norm_num]
    exact paid_terminal_403
  · change terminalPayment 404 ≤ terminalValue ((point cut hi 1024 404+point cut hi 1024 405)/2)
    have hp : terminalPayment 404 = (488566293503:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 404+point cut hi 1024 405)/2 = (179964663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179964663:ℝ)/42188800) = (2310769:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179964663:ℝ)/42188800)-4 = (11209463:ℝ)/42188800 by norm_num]
    exact paid_terminal_404
  · change terminalPayment 405 ≤ terminalValue ((point cut hi 1024 405+point cut hi 1024 406)/2)
    have hp : terminalPayment 405 = (488020363297:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 405+point cut hi 1024 406)/2 = (179989813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((179989813:ℝ)/42188800) = (2309763:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((179989813:ℝ)/42188800)-4 = (11234613:ℝ)/42188800 by norm_num]
    exact paid_terminal_405
  · change terminalPayment 406 ≤ terminalValue ((point cut hi 1024 406+point cut hi 1024 407)/2)
    have hp : terminalPayment 406 = (487473829001:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 406+point cut hi 1024 407)/2 = (180014963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180014963:ℝ)/42188800) = (2308757:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180014963:ℝ)/42188800)-4 = (11259763:ℝ)/42188800 by norm_num]
    exact paid_terminal_406
  · change terminalPayment 407 ≤ terminalValue ((point cut hi 1024 407+point cut hi 1024 408)/2)
    have hp : terminalPayment 407 = (486926689950:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 407+point cut hi 1024 408)/2 = (180040113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180040113:ℝ)/42188800) = (2307751:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180040113:ℝ)/42188800)-4 = (11284913:ℝ)/42188800 by norm_num]
    exact paid_terminal_407
  · change terminalPayment 408 ≤ terminalValue ((point cut hi 1024 408+point cut hi 1024 409)/2)
    have hp : terminalPayment 408 = (486378945480:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 408+point cut hi 1024 409)/2 = (180065263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180065263:ℝ)/42188800) = (2306745:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180065263:ℝ)/42188800)-4 = (11310063:ℝ)/42188800 by norm_num]
    exact paid_terminal_408
  · change terminalPayment 409 ≤ terminalValue ((point cut hi 1024 409+point cut hi 1024 410)/2)
    have hp : terminalPayment 409 = (485830594924:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 409+point cut hi 1024 410)/2 = (180090413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180090413:ℝ)/42188800) = (2305739:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180090413:ℝ)/42188800)-4 = (11335213:ℝ)/42188800 by norm_num]
    exact paid_terminal_409
  · change terminalPayment 410 ≤ terminalValue ((point cut hi 1024 410+point cut hi 1024 411)/2)
    have hp : terminalPayment 410 = (485281637616:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 410+point cut hi 1024 411)/2 = (180115563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180115563:ℝ)/42188800) = (2304733:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180115563:ℝ)/42188800)-4 = (11360363:ℝ)/42188800 by norm_num]
    exact paid_terminal_410
  · change terminalPayment 411 ≤ terminalValue ((point cut hi 1024 411+point cut hi 1024 412)/2)
    have hp : terminalPayment 411 = (484732072885:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 411+point cut hi 1024 412)/2 = (180140713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180140713:ℝ)/42188800) = (2303727:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180140713:ℝ)/42188800)-4 = (11385513:ℝ)/42188800 by norm_num]
    exact paid_terminal_411
  · change terminalPayment 412 ≤ terminalValue ((point cut hi 1024 412+point cut hi 1024 413)/2)
    have hp : terminalPayment 412 = (484181900064:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 412+point cut hi 1024 413)/2 = (180165863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180165863:ℝ)/42188800) = (2302721:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180165863:ℝ)/42188800)-4 = (11410663:ℝ)/42188800 by norm_num]
    exact paid_terminal_412
  · change terminalPayment 413 ≤ terminalValue ((point cut hi 1024 413+point cut hi 1024 414)/2)
    have hp : terminalPayment 413 = (483631118482:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 413+point cut hi 1024 414)/2 = (180191013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180191013:ℝ)/42188800) = (2301715:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180191013:ℝ)/42188800)-4 = (11435813:ℝ)/42188800 by norm_num]
    exact paid_terminal_413
  · change terminalPayment 414 ≤ terminalValue ((point cut hi 1024 414+point cut hi 1024 415)/2)
    have hp : terminalPayment 414 = (483079727465:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 414+point cut hi 1024 415)/2 = (180216163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180216163:ℝ)/42188800) = (2300709:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180216163:ℝ)/42188800)-4 = (11460963:ℝ)/42188800 by norm_num]
    exact paid_terminal_414
  · change terminalPayment 415 ≤ terminalValue ((point cut hi 1024 415+point cut hi 1024 416)/2)
    have hp : terminalPayment 415 = (482527726343:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 415+point cut hi 1024 416)/2 = (180241313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((180241313:ℝ)/42188800) = (2299703:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((180241313:ℝ)/42188800)-4 = (11486113:ℝ)/42188800 by norm_num]
    exact paid_terminal_415
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_025
