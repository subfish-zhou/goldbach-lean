import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints021
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_021 (j : Fin 16) : terminalPayment (16*21+j.val) ≤
    terminalValue ((point cut hi 1024 (16*21+j.val)+point cut hi 1024 (16*21+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 336 ≤ terminalValue ((point cut hi 1024 336+point cut hi 1024 337)/2)
    have hp : terminalPayment 336 = (524307661779:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 336+point cut hi 1024 337)/2 = (178254463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178254463:ℝ)/42188800) = (2379177:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178254463:ℝ)/42188800)-4 = (9499263:ℝ)/42188800 by norm_num]
    exact paid_terminal_336
  · change terminalPayment 337 ≤ terminalValue ((point cut hi 1024 337+point cut hi 1024 338)/2)
    have hp : terminalPayment 337 = (523801310121:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 337+point cut hi 1024 338)/2 = (178279613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178279613:ℝ)/42188800) = (2378171:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178279613:ℝ)/42188800)-4 = (9524413:ℝ)/42188800 by norm_num]
    exact paid_terminal_337
  · change terminalPayment 338 ≤ terminalValue ((point cut hi 1024 338+point cut hi 1024 339)/2)
    have hp : terminalPayment 338 = (523294397054:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 338+point cut hi 1024 339)/2 = (178304763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178304763:ℝ)/42188800) = (2377165:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178304763:ℝ)/42188800)-4 = (9549563:ℝ)/42188800 by norm_num]
    exact paid_terminal_338
  · change terminalPayment 339 ≤ terminalValue ((point cut hi 1024 339+point cut hi 1024 340)/2)
    have hp : terminalPayment 339 = (522786921983:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 339+point cut hi 1024 340)/2 = (178329913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178329913:ℝ)/42188800) = (2376159:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178329913:ℝ)/42188800)-4 = (9574713:ℝ)/42188800 by norm_num]
    exact paid_terminal_339
  · change terminalPayment 340 ≤ terminalValue ((point cut hi 1024 340+point cut hi 1024 341)/2)
    have hp : terminalPayment 340 = (522278884315:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 340+point cut hi 1024 341)/2 = (178355063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178355063:ℝ)/42188800) = (2375153:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178355063:ℝ)/42188800)-4 = (9599863:ℝ)/42188800 by norm_num]
    exact paid_terminal_340
  · change terminalPayment 341 ≤ terminalValue ((point cut hi 1024 341+point cut hi 1024 342)/2)
    have hp : terminalPayment 341 = (521770283454:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 341+point cut hi 1024 342)/2 = (178380213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178380213:ℝ)/42188800) = (2374147:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178380213:ℝ)/42188800)-4 = (9625013:ℝ)/42188800 by norm_num]
    exact paid_terminal_341
  · change terminalPayment 342 ≤ terminalValue ((point cut hi 1024 342+point cut hi 1024 343)/2)
    have hp : terminalPayment 342 = (521261118803:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 342+point cut hi 1024 343)/2 = (178405363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178405363:ℝ)/42188800) = (2373141:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178405363:ℝ)/42188800)-4 = (9650163:ℝ)/42188800 by norm_num]
    exact paid_terminal_342
  · change terminalPayment 343 ≤ terminalValue ((point cut hi 1024 343+point cut hi 1024 344)/2)
    have hp : terminalPayment 343 = (520751389764:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 343+point cut hi 1024 344)/2 = (178430513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178430513:ℝ)/42188800) = (2372135:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178430513:ℝ)/42188800)-4 = (9675313:ℝ)/42188800 by norm_num]
    exact paid_terminal_343
  · change terminalPayment 344 ≤ terminalValue ((point cut hi 1024 344+point cut hi 1024 345)/2)
    have hp : terminalPayment 344 = (520241095740:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 344+point cut hi 1024 345)/2 = (178455663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178455663:ℝ)/42188800) = (2371129:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178455663:ℝ)/42188800)-4 = (9700463:ℝ)/42188800 by norm_num]
    exact paid_terminal_344
  · change terminalPayment 345 ≤ terminalValue ((point cut hi 1024 345+point cut hi 1024 346)/2)
    have hp : terminalPayment 345 = (519730236130:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 345+point cut hi 1024 346)/2 = (178480813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178480813:ℝ)/42188800) = (2370123:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178480813:ℝ)/42188800)-4 = (9725613:ℝ)/42188800 by norm_num]
    exact paid_terminal_345
  · change terminalPayment 346 ≤ terminalValue ((point cut hi 1024 346+point cut hi 1024 347)/2)
    have hp : terminalPayment 346 = (519218810334:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 346+point cut hi 1024 347)/2 = (178505963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178505963:ℝ)/42188800) = (2369117:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178505963:ℝ)/42188800)-4 = (9750763:ℝ)/42188800 by norm_num]
    exact paid_terminal_346
  · change terminalPayment 347 ≤ terminalValue ((point cut hi 1024 347+point cut hi 1024 348)/2)
    have hp : terminalPayment 347 = (518706817751:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 347+point cut hi 1024 348)/2 = (178531113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178531113:ℝ)/42188800) = (2368111:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178531113:ℝ)/42188800)-4 = (9775913:ℝ)/42188800 by norm_num]
    exact paid_terminal_347
  · change terminalPayment 348 ≤ terminalValue ((point cut hi 1024 348+point cut hi 1024 349)/2)
    have hp : terminalPayment 348 = (518194257778:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 348+point cut hi 1024 349)/2 = (178556263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178556263:ℝ)/42188800) = (2367105:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178556263:ℝ)/42188800)-4 = (9801063:ℝ)/42188800 by norm_num]
    exact paid_terminal_348
  · change terminalPayment 349 ≤ terminalValue ((point cut hi 1024 349+point cut hi 1024 350)/2)
    have hp : terminalPayment 349 = (517681129812:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 349+point cut hi 1024 350)/2 = (178581413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178581413:ℝ)/42188800) = (2366099:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178581413:ℝ)/42188800)-4 = (9826213:ℝ)/42188800 by norm_num]
    exact paid_terminal_349
  · change terminalPayment 350 ≤ terminalValue ((point cut hi 1024 350+point cut hi 1024 351)/2)
    have hp : terminalPayment 350 = (517167433247:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 350+point cut hi 1024 351)/2 = (178606563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178606563:ℝ)/42188800) = (2365093:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178606563:ℝ)/42188800)-4 = (9851363:ℝ)/42188800 by norm_num]
    exact paid_terminal_350
  · change terminalPayment 351 ≤ terminalValue ((point cut hi 1024 351+point cut hi 1024 352)/2)
    have hp : terminalPayment 351 = (516653167479:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 351+point cut hi 1024 352)/2 = (178631713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((178631713:ℝ)/42188800) = (2364087:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((178631713:ℝ)/42188800)-4 = (9876513:ℝ)/42188800 by norm_num]
    exact paid_terminal_351
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_021
