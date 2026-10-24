import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints008
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_008 (j : Fin 16) : terminalPayment (16*8+j.val) ≤
    terminalValue ((point cut hi 1024 (16*8+j.val)+point cut hi 1024 (16*8+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 128 ≤ terminalValue ((point cut hi 1024 128+point cut hi 1024 129)/2)
    have hp : terminalPayment 128 = (618255358806:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 128+point cut hi 1024 129)/2 = (173023263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173023263:ℝ)/42188800) = (2588425:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173023263:ℝ)/42188800)-4 = (4268063:ℝ)/42188800 by norm_num]
    exact paid_terminal_128
  · change terminalPayment 129 ≤ terminalValue ((point cut hi 1024 129+point cut hi 1024 130)/2)
    have hp : terminalPayment 129 = (617854256625:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 129+point cut hi 1024 130)/2 = (173048413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173048413:ℝ)/42188800) = (2587419:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173048413:ℝ)/42188800)-4 = (4293213:ℝ)/42188800 by norm_num]
    exact paid_terminal_129
  · change terminalPayment 130 ≤ terminalValue ((point cut hi 1024 130+point cut hi 1024 131)/2)
    have hp : terminalPayment 130 = (617452697284:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 130+point cut hi 1024 131)/2 = (173073563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173073563:ℝ)/42188800) = (2586413:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173073563:ℝ)/42188800)-4 = (4318363:ℝ)/42188800 by norm_num]
    exact paid_terminal_130
  · change terminalPayment 131 ≤ terminalValue ((point cut hi 1024 131+point cut hi 1024 132)/2)
    have hp : terminalPayment 131 = (617050680367:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 131+point cut hi 1024 132)/2 = (173098713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173098713:ℝ)/42188800) = (2585407:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173098713:ℝ)/42188800)-4 = (4343513:ℝ)/42188800 by norm_num]
    exact paid_terminal_131
  · change terminalPayment 132 ≤ terminalValue ((point cut hi 1024 132+point cut hi 1024 133)/2)
    have hp : terminalPayment 132 = (616648205452:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 132+point cut hi 1024 133)/2 = (173123863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173123863:ℝ)/42188800) = (2584401:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173123863:ℝ)/42188800)-4 = (4368663:ℝ)/42188800 by norm_num]
    exact paid_terminal_132
  · change terminalPayment 133 ≤ terminalValue ((point cut hi 1024 133+point cut hi 1024 134)/2)
    have hp : terminalPayment 133 = (616245272121:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 133+point cut hi 1024 134)/2 = (173149013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173149013:ℝ)/42188800) = (2583395:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173149013:ℝ)/42188800)-4 = (4393813:ℝ)/42188800 by norm_num]
    exact paid_terminal_133
  · change terminalPayment 134 ≤ terminalValue ((point cut hi 1024 134+point cut hi 1024 135)/2)
    have hp : terminalPayment 134 = (615841879954:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 134+point cut hi 1024 135)/2 = (173174163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173174163:ℝ)/42188800) = (2582389:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173174163:ℝ)/42188800)-4 = (4418963:ℝ)/42188800 by norm_num]
    exact paid_terminal_134
  · change terminalPayment 135 ≤ terminalValue ((point cut hi 1024 135+point cut hi 1024 136)/2)
    have hp : terminalPayment 135 = (615438028528:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 135+point cut hi 1024 136)/2 = (173199313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173199313:ℝ)/42188800) = (2581383:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173199313:ℝ)/42188800)-4 = (4444113:ℝ)/42188800 by norm_num]
    exact paid_terminal_135
  · change terminalPayment 136 ≤ terminalValue ((point cut hi 1024 136+point cut hi 1024 137)/2)
    have hp : terminalPayment 136 = (615033717421:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 136+point cut hi 1024 137)/2 = (173224463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173224463:ℝ)/42188800) = (2580377:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173224463:ℝ)/42188800)-4 = (4469263:ℝ)/42188800 by norm_num]
    exact paid_terminal_136
  · change terminalPayment 137 ≤ terminalValue ((point cut hi 1024 137+point cut hi 1024 138)/2)
    have hp : terminalPayment 137 = (614628946211:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 137+point cut hi 1024 138)/2 = (173249613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173249613:ℝ)/42188800) = (2579371:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173249613:ℝ)/42188800)-4 = (4494413:ℝ)/42188800 by norm_num]
    exact paid_terminal_137
  · change terminalPayment 138 ≤ terminalValue ((point cut hi 1024 138+point cut hi 1024 139)/2)
    have hp : terminalPayment 138 = (614223714475:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 138+point cut hi 1024 139)/2 = (173274763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173274763:ℝ)/42188800) = (2578365:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173274763:ℝ)/42188800)-4 = (4519563:ℝ)/42188800 by norm_num]
    exact paid_terminal_138
  · change terminalPayment 139 ≤ terminalValue ((point cut hi 1024 139+point cut hi 1024 140)/2)
    have hp : terminalPayment 139 = (613818021787:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 139+point cut hi 1024 140)/2 = (173299913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173299913:ℝ)/42188800) = (2577359:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173299913:ℝ)/42188800)-4 = (4544713:ℝ)/42188800 by norm_num]
    exact paid_terminal_139
  · change terminalPayment 140 ≤ terminalValue ((point cut hi 1024 140+point cut hi 1024 141)/2)
    have hp : terminalPayment 140 = (613411867723:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 140+point cut hi 1024 141)/2 = (173325063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173325063:ℝ)/42188800) = (2576353:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173325063:ℝ)/42188800)-4 = (4569863:ℝ)/42188800 by norm_num]
    exact paid_terminal_140
  · change terminalPayment 141 ≤ terminalValue ((point cut hi 1024 141+point cut hi 1024 142)/2)
    have hp : terminalPayment 141 = (613005251858:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 141+point cut hi 1024 142)/2 = (173350213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173350213:ℝ)/42188800) = (2575347:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173350213:ℝ)/42188800)-4 = (4595013:ℝ)/42188800 by norm_num]
    exact paid_terminal_141
  · change terminalPayment 142 ≤ terminalValue ((point cut hi 1024 142+point cut hi 1024 143)/2)
    have hp : terminalPayment 142 = (612598173764:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 142+point cut hi 1024 143)/2 = (173375363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173375363:ℝ)/42188800) = (2574341:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173375363:ℝ)/42188800)-4 = (4620163:ℝ)/42188800 by norm_num]
    exact paid_terminal_142
  · change terminalPayment 143 ≤ terminalValue ((point cut hi 1024 143+point cut hi 1024 144)/2)
    have hp : terminalPayment 143 = (612190633015:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 143+point cut hi 1024 144)/2 = (173400513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((173400513:ℝ)/42188800) = (2573335:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((173400513:ℝ)/42188800)-4 = (4645313:ℝ)/42188800 by norm_num]
    exact paid_terminal_143
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_008
