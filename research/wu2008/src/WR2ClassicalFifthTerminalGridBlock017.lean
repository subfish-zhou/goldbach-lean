import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints017
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_017 (j : Fin 16) : terminalPayment (16*17+j.val) ≤
    terminalValue ((point cut hi 1024 (16*17+j.val)+point cut hi 1024 (16*17+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 272 ≤ terminalValue ((point cut hi 1024 272+point cut hi 1024 273)/2)
    have hp : terminalPayment 272 = (555572863659:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 272+point cut hi 1024 273)/2 = (176644863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176644863:ℝ)/42188800) = (2443561:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176644863:ℝ)/42188800)-4 = (7889663:ℝ)/42188800 by norm_num]
    exact paid_terminal_272
  · change terminalPayment 273 ≤ terminalValue ((point cut hi 1024 273+point cut hi 1024 274)/2)
    have hp : terminalPayment 273 = (555101251229:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 273+point cut hi 1024 274)/2 = (176670013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176670013:ℝ)/42188800) = (2442555:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176670013:ℝ)/42188800)-4 = (7914813:ℝ)/42188800 by norm_num]
    exact paid_terminal_273
  · change terminalPayment 274 ≤ terminalValue ((point cut hi 1024 274+point cut hi 1024 275)/2)
    have hp : terminalPayment 274 = (554629113410:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 274+point cut hi 1024 275)/2 = (176695163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176695163:ℝ)/42188800) = (2441549:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176695163:ℝ)/42188800)-4 = (7939963:ℝ)/42188800 by norm_num]
    exact paid_terminal_274
  · change terminalPayment 275 ≤ terminalValue ((point cut hi 1024 275+point cut hi 1024 276)/2)
    have hp : terminalPayment 275 = (554156449666:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 275+point cut hi 1024 276)/2 = (176720313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176720313:ℝ)/42188800) = (2440543:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176720313:ℝ)/42188800)-4 = (7965113:ℝ)/42188800 by norm_num]
    exact paid_terminal_275
  · change terminalPayment 276 ≤ terminalValue ((point cut hi 1024 276+point cut hi 1024 277)/2)
    have hp : terminalPayment 276 = (553683259463:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 276+point cut hi 1024 277)/2 = (176745463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176745463:ℝ)/42188800) = (2439537:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176745463:ℝ)/42188800)-4 = (7990263:ℝ)/42188800 by norm_num]
    exact paid_terminal_276
  · change terminalPayment 277 ≤ terminalValue ((point cut hi 1024 277+point cut hi 1024 278)/2)
    have hp : terminalPayment 277 = (553209542266:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 277+point cut hi 1024 278)/2 = (176770613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176770613:ℝ)/42188800) = (2438531:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176770613:ℝ)/42188800)-4 = (8015413:ℝ)/42188800 by norm_num]
    exact paid_terminal_277
  · change terminalPayment 278 ≤ terminalValue ((point cut hi 1024 278+point cut hi 1024 279)/2)
    have hp : terminalPayment 278 = (552735297538:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 278+point cut hi 1024 279)/2 = (176795763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176795763:ℝ)/42188800) = (2437525:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176795763:ℝ)/42188800)-4 = (8040563:ℝ)/42188800 by norm_num]
    exact paid_terminal_278
  · change terminalPayment 279 ≤ terminalValue ((point cut hi 1024 279+point cut hi 1024 280)/2)
    have hp : terminalPayment 279 = (552260524741:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 279+point cut hi 1024 280)/2 = (176820913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176820913:ℝ)/42188800) = (2436519:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176820913:ℝ)/42188800)-4 = (8065713:ℝ)/42188800 by norm_num]
    exact paid_terminal_279
  · change terminalPayment 280 ≤ terminalValue ((point cut hi 1024 280+point cut hi 1024 281)/2)
    have hp : terminalPayment 280 = (551785223337:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 280+point cut hi 1024 281)/2 = (176846063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176846063:ℝ)/42188800) = (2435513:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176846063:ℝ)/42188800)-4 = (8090863:ℝ)/42188800 by norm_num]
    exact paid_terminal_280
  · change terminalPayment 281 ≤ terminalValue ((point cut hi 1024 281+point cut hi 1024 282)/2)
    have hp : terminalPayment 281 = (551309392787:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 281+point cut hi 1024 282)/2 = (176871213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176871213:ℝ)/42188800) = (2434507:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176871213:ℝ)/42188800)-4 = (8116013:ℝ)/42188800 by norm_num]
    exact paid_terminal_281
  · change terminalPayment 282 ≤ terminalValue ((point cut hi 1024 282+point cut hi 1024 283)/2)
    have hp : terminalPayment 282 = (550833032551:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 282+point cut hi 1024 283)/2 = (176896363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176896363:ℝ)/42188800) = (2433501:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176896363:ℝ)/42188800)-4 = (8141163:ℝ)/42188800 by norm_num]
    exact paid_terminal_282
  · change terminalPayment 283 ≤ terminalValue ((point cut hi 1024 283+point cut hi 1024 284)/2)
    have hp : terminalPayment 283 = (550356142087:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 283+point cut hi 1024 284)/2 = (176921513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176921513:ℝ)/42188800) = (2432495:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176921513:ℝ)/42188800)-4 = (8166313:ℝ)/42188800 by norm_num]
    exact paid_terminal_283
  · change terminalPayment 284 ≤ terminalValue ((point cut hi 1024 284+point cut hi 1024 285)/2)
    have hp : terminalPayment 284 = (549878720854:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 284+point cut hi 1024 285)/2 = (176946663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176946663:ℝ)/42188800) = (2431489:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176946663:ℝ)/42188800)-4 = (8191463:ℝ)/42188800 by norm_num]
    exact paid_terminal_284
  · change terminalPayment 285 ≤ terminalValue ((point cut hi 1024 285+point cut hi 1024 286)/2)
    have hp : terminalPayment 285 = (549400768308:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 285+point cut hi 1024 286)/2 = (176971813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176971813:ℝ)/42188800) = (2430483:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176971813:ℝ)/42188800)-4 = (8216613:ℝ)/42188800 by norm_num]
    exact paid_terminal_285
  · change terminalPayment 286 ≤ terminalValue ((point cut hi 1024 286+point cut hi 1024 287)/2)
    have hp : terminalPayment 286 = (548922283907:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 286+point cut hi 1024 287)/2 = (176996963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((176996963:ℝ)/42188800) = (2429477:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((176996963:ℝ)/42188800)-4 = (8241763:ℝ)/42188800 by norm_num]
    exact paid_terminal_286
  · change terminalPayment 287 ≤ terminalValue ((point cut hi 1024 287+point cut hi 1024 288)/2)
    have hp : terminalPayment 287 = (548443267105:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 287+point cut hi 1024 288)/2 = (177022113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177022113:ℝ)/42188800) = (2428471:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177022113:ℝ)/42188800)-4 = (8266913:ℝ)/42188800 by norm_num]
    exact paid_terminal_287
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_017
