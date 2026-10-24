import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints042
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_042 (j : Fin 16) : terminalPayment (16*42+j.val) ≤
    terminalValue ((point cut hi 1024 (16*42+j.val)+point cut hi 1024 (16*42+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 672 ≤ terminalValue ((point cut hi 1024 672+point cut hi 1024 673)/2)
    have hp : terminalPayment 672 = (318284513977:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 672+point cut hi 1024 673)/2 = (186704863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186704863:ℝ)/42188800) = (2041161:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186704863:ℝ)/42188800)-4 = (17949663:ℝ)/42188800 by norm_num]
    exact paid_terminal_672
  · change terminalPayment 673 ≤ terminalValue ((point cut hi 1024 673+point cut hi 1024 674)/2)
    have hp : terminalPayment 673 = (317549017107:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 673+point cut hi 1024 674)/2 = (186730013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186730013:ℝ)/42188800) = (2040155:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186730013:ℝ)/42188800)-4 = (17974813:ℝ)/42188800 by norm_num]
    exact paid_terminal_673
  · change terminalPayment 674 ≤ terminalValue ((point cut hi 1024 674+point cut hi 1024 675)/2)
    have hp : terminalPayment 674 = (316812692158:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 674+point cut hi 1024 675)/2 = (186755163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186755163:ℝ)/42188800) = (2039149:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186755163:ℝ)/42188800)-4 = (17999963:ℝ)/42188800 by norm_num]
    exact paid_terminal_674
  · change terminalPayment 675 ≤ terminalValue ((point cut hi 1024 675+point cut hi 1024 676)/2)
    have hp : terminalPayment 675 = (316075538093:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 675+point cut hi 1024 676)/2 = (186780313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186780313:ℝ)/42188800) = (2038143:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186780313:ℝ)/42188800)-4 = (18025113:ℝ)/42188800 by norm_num]
    exact paid_terminal_675
  · change terminalPayment 676 ≤ terminalValue ((point cut hi 1024 676+point cut hi 1024 677)/2)
    have hp : terminalPayment 676 = (315337553869:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 676+point cut hi 1024 677)/2 = (186805463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186805463:ℝ)/42188800) = (2037137:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186805463:ℝ)/42188800)-4 = (18050263:ℝ)/42188800 by norm_num]
    exact paid_terminal_676
  · change terminalPayment 677 ≤ terminalValue ((point cut hi 1024 677+point cut hi 1024 678)/2)
    have hp : terminalPayment 677 = (314598738445:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 677+point cut hi 1024 678)/2 = (186830613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186830613:ℝ)/42188800) = (2036131:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186830613:ℝ)/42188800)-4 = (18075413:ℝ)/42188800 by norm_num]
    exact paid_terminal_677
  · change terminalPayment 678 ≤ terminalValue ((point cut hi 1024 678+point cut hi 1024 679)/2)
    have hp : terminalPayment 678 = (313859090775:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 678+point cut hi 1024 679)/2 = (186855763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186855763:ℝ)/42188800) = (2035125:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186855763:ℝ)/42188800)-4 = (18100563:ℝ)/42188800 by norm_num]
    exact paid_terminal_678
  · change terminalPayment 679 ≤ terminalValue ((point cut hi 1024 679+point cut hi 1024 680)/2)
    have hp : terminalPayment 679 = (313118609813:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 679+point cut hi 1024 680)/2 = (186880913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186880913:ℝ)/42188800) = (2034119:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186880913:ℝ)/42188800)-4 = (18125713:ℝ)/42188800 by norm_num]
    exact paid_terminal_679
  · change terminalPayment 680 ≤ terminalValue ((point cut hi 1024 680+point cut hi 1024 681)/2)
    have hp : terminalPayment 680 = (312377294512:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 680+point cut hi 1024 681)/2 = (186906063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186906063:ℝ)/42188800) = (2033113:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186906063:ℝ)/42188800)-4 = (18150863:ℝ)/42188800 by norm_num]
    exact paid_terminal_680
  · change terminalPayment 681 ≤ terminalValue ((point cut hi 1024 681+point cut hi 1024 682)/2)
    have hp : terminalPayment 681 = (311635143820:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 681+point cut hi 1024 682)/2 = (186931213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186931213:ℝ)/42188800) = (2032107:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186931213:ℝ)/42188800)-4 = (18176013:ℝ)/42188800 by norm_num]
    exact paid_terminal_681
  · change terminalPayment 682 ≤ terminalValue ((point cut hi 1024 682+point cut hi 1024 683)/2)
    have hp : terminalPayment 682 = (310892156687:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 682+point cut hi 1024 683)/2 = (186956363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186956363:ℝ)/42188800) = (2031101:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186956363:ℝ)/42188800)-4 = (18201163:ℝ)/42188800 by norm_num]
    exact paid_terminal_682
  · change terminalPayment 683 ≤ terminalValue ((point cut hi 1024 683+point cut hi 1024 684)/2)
    have hp : terminalPayment 683 = (310148332058:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 683+point cut hi 1024 684)/2 = (186981513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186981513:ℝ)/42188800) = (2030095:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186981513:ℝ)/42188800)-4 = (18226313:ℝ)/42188800 by norm_num]
    exact paid_terminal_683
  · change terminalPayment 684 ≤ terminalValue ((point cut hi 1024 684+point cut hi 1024 685)/2)
    have hp : terminalPayment 684 = (309403668879:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 684+point cut hi 1024 685)/2 = (187006663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187006663:ℝ)/42188800) = (2029089:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187006663:ℝ)/42188800)-4 = (18251463:ℝ)/42188800 by norm_num]
    exact paid_terminal_684
  · change terminalPayment 685 ≤ terminalValue ((point cut hi 1024 685+point cut hi 1024 686)/2)
    have hp : terminalPayment 685 = (308658166092:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 685+point cut hi 1024 686)/2 = (187031813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187031813:ℝ)/42188800) = (2028083:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187031813:ℝ)/42188800)-4 = (18276613:ℝ)/42188800 by norm_num]
    exact paid_terminal_685
  · change terminalPayment 686 ≤ terminalValue ((point cut hi 1024 686+point cut hi 1024 687)/2)
    have hp : terminalPayment 686 = (307911822639:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 686+point cut hi 1024 687)/2 = (187056963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187056963:ℝ)/42188800) = (2027077:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187056963:ℝ)/42188800)-4 = (18301763:ℝ)/42188800 by norm_num]
    exact paid_terminal_686
  · change terminalPayment 687 ≤ terminalValue ((point cut hi 1024 687+point cut hi 1024 688)/2)
    have hp : terminalPayment 687 = (307164637458:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 687+point cut hi 1024 688)/2 = (187082113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187082113:ℝ)/42188800) = (2026071:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187082113:ℝ)/42188800)-4 = (18326913:ℝ)/42188800 by norm_num]
    exact paid_terminal_687
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_042
