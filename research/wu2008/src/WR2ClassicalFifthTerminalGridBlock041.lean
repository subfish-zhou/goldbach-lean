import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints041
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_041 (j : Fin 16) : terminalPayment (16*41+j.val) ≤
    terminalValue ((point cut hi 1024 (16*41+j.val)+point cut hi 1024 (16*41+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 656 ≤ terminalValue ((point cut hi 1024 656+point cut hi 1024 657)/2)
    have hp : terminalPayment 656 = (329940686475:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 656+point cut hi 1024 657)/2 = (186302463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186302463:ℝ)/42188800) = (2057257:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186302463:ℝ)/42188800)-4 = (17547263:ℝ)/42188800 by norm_num]
    exact paid_terminal_656
  · change terminalPayment 657 ≤ terminalValue ((point cut hi 1024 657+point cut hi 1024 658)/2)
    have hp : terminalPayment 657 = (329218298956:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 657+point cut hi 1024 658)/2 = (186327613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186327613:ℝ)/42188800) = (2056251:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186327613:ℝ)/42188800)-4 = (17572413:ℝ)/42188800 by norm_num]
    exact paid_terminal_657
  · change terminalPayment 658 ≤ terminalValue ((point cut hi 1024 658+point cut hi 1024 659)/2)
    have hp : terminalPayment 658 = (328495099747:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 658+point cut hi 1024 659)/2 = (186352763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186352763:ℝ)/42188800) = (2055245:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186352763:ℝ)/42188800)-4 = (17597563:ℝ)/42188800 by norm_num]
    exact paid_terminal_658
  · change terminalPayment 659 ≤ terminalValue ((point cut hi 1024 659+point cut hi 1024 660)/2)
    have hp : terminalPayment 659 = (327771087836:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 659+point cut hi 1024 660)/2 = (186377913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186377913:ℝ)/42188800) = (2054239:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186377913:ℝ)/42188800)-4 = (17622713:ℝ)/42188800 by norm_num]
    exact paid_terminal_659
  · change terminalPayment 660 ≤ terminalValue ((point cut hi 1024 660+point cut hi 1024 661)/2)
    have hp : terminalPayment 660 = (327046262213:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 660+point cut hi 1024 661)/2 = (186403063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186403063:ℝ)/42188800) = (2053233:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186403063:ℝ)/42188800)-4 = (17647863:ℝ)/42188800 by norm_num]
    exact paid_terminal_660
  · change terminalPayment 661 ≤ terminalValue ((point cut hi 1024 661+point cut hi 1024 662)/2)
    have hp : terminalPayment 661 = (326320621860:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 661+point cut hi 1024 662)/2 = (186428213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186428213:ℝ)/42188800) = (2052227:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186428213:ℝ)/42188800)-4 = (17673013:ℝ)/42188800 by norm_num]
    exact paid_terminal_661
  · change terminalPayment 662 ≤ terminalValue ((point cut hi 1024 662+point cut hi 1024 663)/2)
    have hp : terminalPayment 662 = (325594165763:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 662+point cut hi 1024 663)/2 = (186453363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186453363:ℝ)/42188800) = (2051221:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186453363:ℝ)/42188800)-4 = (17698163:ℝ)/42188800 by norm_num]
    exact paid_terminal_662
  · change terminalPayment 663 ≤ terminalValue ((point cut hi 1024 663+point cut hi 1024 664)/2)
    have hp : terminalPayment 663 = (324866892903:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 663+point cut hi 1024 664)/2 = (1810471:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((1810471:ℝ)/409600) = (19905:ℝ)/16384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((1810471:ℝ)/409600)-4 = (172071:ℝ)/409600 by norm_num]
    exact paid_terminal_663
  · change terminalPayment 664 ≤ terminalValue ((point cut hi 1024 664+point cut hi 1024 665)/2)
    have hp : terminalPayment 664 = (324138802261:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 664+point cut hi 1024 665)/2 = (186503663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186503663:ℝ)/42188800) = (2049209:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186503663:ℝ)/42188800)-4 = (17748463:ℝ)/42188800 by norm_num]
    exact paid_terminal_664
  · change terminalPayment 665 ≤ terminalValue ((point cut hi 1024 665+point cut hi 1024 666)/2)
    have hp : terminalPayment 665 = (323409892814:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 665+point cut hi 1024 666)/2 = (186528813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186528813:ℝ)/42188800) = (2048203:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186528813:ℝ)/42188800)-4 = (17773613:ℝ)/42188800 by norm_num]
    exact paid_terminal_665
  · change terminalPayment 666 ≤ terminalValue ((point cut hi 1024 666+point cut hi 1024 667)/2)
    have hp : terminalPayment 666 = (322680163539:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 666+point cut hi 1024 667)/2 = (186553963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186553963:ℝ)/42188800) = (2047197:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186553963:ℝ)/42188800)-4 = (17798763:ℝ)/42188800 by norm_num]
    exact paid_terminal_666
  · change terminalPayment 667 ≤ terminalValue ((point cut hi 1024 667+point cut hi 1024 668)/2)
    have hp : terminalPayment 667 = (321949613411:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 667+point cut hi 1024 668)/2 = (186579113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186579113:ℝ)/42188800) = (2046191:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186579113:ℝ)/42188800)-4 = (17823913:ℝ)/42188800 by norm_num]
    exact paid_terminal_667
  · change terminalPayment 668 ≤ terminalValue ((point cut hi 1024 668+point cut hi 1024 669)/2)
    have hp : terminalPayment 668 = (321218241403:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 668+point cut hi 1024 669)/2 = (186604263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186604263:ℝ)/42188800) = (2045185:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186604263:ℝ)/42188800)-4 = (17849063:ℝ)/42188800 by norm_num]
    exact paid_terminal_668
  · change terminalPayment 669 ≤ terminalValue ((point cut hi 1024 669+point cut hi 1024 670)/2)
    have hp : terminalPayment 669 = (320486046488:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 669+point cut hi 1024 670)/2 = (186629413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186629413:ℝ)/42188800) = (2044179:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186629413:ℝ)/42188800)-4 = (17874213:ℝ)/42188800 by norm_num]
    exact paid_terminal_669
  · change terminalPayment 670 ≤ terminalValue ((point cut hi 1024 670+point cut hi 1024 671)/2)
    have hp : terminalPayment 670 = (319753027633:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 670+point cut hi 1024 671)/2 = (186654563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186654563:ℝ)/42188800) = (2043173:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186654563:ℝ)/42188800)-4 = (17899363:ℝ)/42188800 by norm_num]
    exact paid_terminal_670
  · change terminalPayment 671 ≤ terminalValue ((point cut hi 1024 671+point cut hi 1024 672)/2)
    have hp : terminalPayment 671 = (319019183808:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 671+point cut hi 1024 672)/2 = (186679713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186679713:ℝ)/42188800) = (2042167:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186679713:ℝ)/42188800)-4 = (17924513:ℝ)/42188800 by norm_num]
    exact paid_terminal_671
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_041
