import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints019
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_019 (j : Fin 16) : terminalPayment (16*19+j.val) ≤
    terminalValue ((point cut hi 1024 (16*19+j.val)+point cut hi 1024 (16*19+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 304 ≤ terminalValue ((point cut hi 1024 304+point cut hi 1024 305)/2)
    have hp : terminalPayment 304 = (540217991981:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 304+point cut hi 1024 305)/2 = (177449663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177449663:ℝ)/42188800) = (2411369:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177449663:ℝ)/42188800)-4 = (8694463:ℝ)/42188800 by norm_num]
    exact paid_terminal_304
  · change terminalPayment 305 ≤ terminalValue ((point cut hi 1024 305+point cut hi 1024 306)/2)
    have hp : terminalPayment 305 = (539729297791:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 305+point cut hi 1024 306)/2 = (177474813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177474813:ℝ)/42188800) = (2410363:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177474813:ℝ)/42188800)-4 = (8719613:ℝ)/42188800 by norm_num]
    exact paid_terminal_305
  · change terminalPayment 306 ≤ terminalValue ((point cut hi 1024 306+point cut hi 1024 307)/2)
    have hp : terminalPayment 306 = (539240060679:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 306+point cut hi 1024 307)/2 = (177499963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177499963:ℝ)/42188800) = (2409357:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177499963:ℝ)/42188800)-4 = (8744763:ℝ)/42188800 by norm_num]
    exact paid_terminal_306
  · change terminalPayment 307 ≤ terminalValue ((point cut hi 1024 307+point cut hi 1024 308)/2)
    have hp : terminalPayment 307 = (538750280081:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 307+point cut hi 1024 308)/2 = (177525113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177525113:ℝ)/42188800) = (2408351:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177525113:ℝ)/42188800)-4 = (8769913:ℝ)/42188800 by norm_num]
    exact paid_terminal_307
  · change terminalPayment 308 ≤ terminalValue ((point cut hi 1024 308+point cut hi 1024 309)/2)
    have hp : terminalPayment 308 = (538259955432:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 308+point cut hi 1024 309)/2 = (177550263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177550263:ℝ)/42188800) = (2407345:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177550263:ℝ)/42188800)-4 = (8795063:ℝ)/42188800 by norm_num]
    exact paid_terminal_308
  · change terminalPayment 309 ≤ terminalValue ((point cut hi 1024 309+point cut hi 1024 310)/2)
    have hp : terminalPayment 309 = (537769086170:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 309+point cut hi 1024 310)/2 = (177575413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177575413:ℝ)/42188800) = (2406339:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177575413:ℝ)/42188800)-4 = (8820213:ℝ)/42188800 by norm_num]
    exact paid_terminal_309
  · change terminalPayment 310 ≤ terminalValue ((point cut hi 1024 310+point cut hi 1024 311)/2)
    have hp : terminalPayment 310 = (537277671726:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 310+point cut hi 1024 311)/2 = (177600563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177600563:ℝ)/42188800) = (2405333:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177600563:ℝ)/42188800)-4 = (8845363:ℝ)/42188800 by norm_num]
    exact paid_terminal_310
  · change terminalPayment 311 ≤ terminalValue ((point cut hi 1024 311+point cut hi 1024 312)/2)
    have hp : terminalPayment 311 = (536785711536:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 311+point cut hi 1024 312)/2 = (177625713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177625713:ℝ)/42188800) = (2404327:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177625713:ℝ)/42188800)-4 = (8870513:ℝ)/42188800 by norm_num]
    exact paid_terminal_311
  · change terminalPayment 312 ≤ terminalValue ((point cut hi 1024 312+point cut hi 1024 313)/2)
    have hp : terminalPayment 312 = (536293205031:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 312+point cut hi 1024 313)/2 = (177650863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177650863:ℝ)/42188800) = (2403321:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177650863:ℝ)/42188800)-4 = (8895663:ℝ)/42188800 by norm_num]
    exact paid_terminal_312
  · change terminalPayment 313 ≤ terminalValue ((point cut hi 1024 313+point cut hi 1024 314)/2)
    have hp : terminalPayment 313 = (535800151642:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 313+point cut hi 1024 314)/2 = (177676013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177676013:ℝ)/42188800) = (2402315:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177676013:ℝ)/42188800)-4 = (8920813:ℝ)/42188800 by norm_num]
    exact paid_terminal_313
  · change terminalPayment 314 ≤ terminalValue ((point cut hi 1024 314+point cut hi 1024 315)/2)
    have hp : terminalPayment 314 = (535306550799:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 314+point cut hi 1024 315)/2 = (177701163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177701163:ℝ)/42188800) = (2401309:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177701163:ℝ)/42188800)-4 = (8945963:ℝ)/42188800 by norm_num]
    exact paid_terminal_314
  · change terminalPayment 315 ≤ terminalValue ((point cut hi 1024 315+point cut hi 1024 316)/2)
    have hp : terminalPayment 315 = (534812401934:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 315+point cut hi 1024 316)/2 = (177726313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177726313:ℝ)/42188800) = (2400303:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177726313:ℝ)/42188800)-4 = (8971113:ℝ)/42188800 by norm_num]
    exact paid_terminal_315
  · change terminalPayment 316 ≤ terminalValue ((point cut hi 1024 316+point cut hi 1024 317)/2)
    have hp : terminalPayment 316 = (534317704473:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 316+point cut hi 1024 317)/2 = (177751463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177751463:ℝ)/42188800) = (2399297:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177751463:ℝ)/42188800)-4 = (8996263:ℝ)/42188800 by norm_num]
    exact paid_terminal_316
  · change terminalPayment 317 ≤ terminalValue ((point cut hi 1024 317+point cut hi 1024 318)/2)
    have hp : terminalPayment 317 = (533822457844:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 317+point cut hi 1024 318)/2 = (177776613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177776613:ℝ)/42188800) = (2398291:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177776613:ℝ)/42188800)-4 = (9021413:ℝ)/42188800 by norm_num]
    exact paid_terminal_317
  · change terminalPayment 318 ≤ terminalValue ((point cut hi 1024 318+point cut hi 1024 319)/2)
    have hp : terminalPayment 318 = (533326661475:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 318+point cut hi 1024 319)/2 = (177801763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177801763:ℝ)/42188800) = (2397285:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177801763:ℝ)/42188800)-4 = (9046563:ℝ)/42188800 by norm_num]
    exact paid_terminal_318
  · change terminalPayment 319 ≤ terminalValue ((point cut hi 1024 319+point cut hi 1024 320)/2)
    have hp : terminalPayment 319 = (532830314790:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 319+point cut hi 1024 320)/2 = (177826913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((177826913:ℝ)/42188800) = (2396279:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((177826913:ℝ)/42188800)-4 = (9071713:ℝ)/42188800 by norm_num]
    exact paid_terminal_319
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_019
