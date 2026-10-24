import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints040
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_040 (j : Fin 16) : terminalPayment (16*40+j.val) ≤
    terminalValue ((point cut hi 1024 (16*40+j.val)+point cut hi 1024 (16*40+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 640 ≤ terminalValue ((point cut hi 1024 640+point cut hi 1024 641)/2)
    have hp : terminalPayment 640 = (341389315512:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 640+point cut hi 1024 641)/2 = (185900063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185900063:ℝ)/42188800) = (2073353:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185900063:ℝ)/42188800)-4 = (17144863:ℝ)/42188800 by norm_num]
    exact paid_terminal_640
  · change terminalPayment 641 ≤ terminalValue ((point cut hi 1024 641+point cut hi 1024 642)/2)
    have hp : terminalPayment 641 = (340679778897:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 641+point cut hi 1024 642)/2 = (185925213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185925213:ℝ)/42188800) = (2072347:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185925213:ℝ)/42188800)-4 = (17170013:ℝ)/42188800 by norm_num]
    exact paid_terminal_641
  · change terminalPayment 642 ≤ terminalValue ((point cut hi 1024 642+point cut hi 1024 643)/2)
    have hp : terminalPayment 642 = (339969446540:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 642+point cut hi 1024 643)/2 = (185950363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185950363:ℝ)/42188800) = (2071341:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185950363:ℝ)/42188800)-4 = (17195163:ℝ)/42188800 by norm_num]
    exact paid_terminal_642
  · change terminalPayment 643 ≤ terminalValue ((point cut hi 1024 643+point cut hi 1024 644)/2)
    have hp : terminalPayment 643 = (339258317456:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 643+point cut hi 1024 644)/2 = (185975513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((185975513:ℝ)/42188800) = (2070335:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((185975513:ℝ)/42188800)-4 = (17220313:ℝ)/42188800 by norm_num]
    exact paid_terminal_643
  · change terminalPayment 644 ≤ terminalValue ((point cut hi 1024 644+point cut hi 1024 645)/2)
    have hp : terminalPayment 644 = (338546390661:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 644+point cut hi 1024 645)/2 = (186000663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186000663:ℝ)/42188800) = (2069329:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186000663:ℝ)/42188800)-4 = (17245463:ℝ)/42188800 by norm_num]
    exact paid_terminal_644
  · change terminalPayment 645 ≤ terminalValue ((point cut hi 1024 645+point cut hi 1024 646)/2)
    have hp : terminalPayment 645 = (337833665166:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 645+point cut hi 1024 646)/2 = (186025813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186025813:ℝ)/42188800) = (2068323:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186025813:ℝ)/42188800)-4 = (17270613:ℝ)/42188800 by norm_num]
    exact paid_terminal_645
  · change terminalPayment 646 ≤ terminalValue ((point cut hi 1024 646+point cut hi 1024 647)/2)
    have hp : terminalPayment 646 = (337120139982:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 646+point cut hi 1024 647)/2 = (186050963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186050963:ℝ)/42188800) = (2067317:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186050963:ℝ)/42188800)-4 = (17295763:ℝ)/42188800 by norm_num]
    exact paid_terminal_646
  · change terminalPayment 647 ≤ terminalValue ((point cut hi 1024 647+point cut hi 1024 648)/2)
    have hp : terminalPayment 647 = (336405814119:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 647+point cut hi 1024 648)/2 = (186076113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186076113:ℝ)/42188800) = (2066311:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186076113:ℝ)/42188800)-4 = (17320913:ℝ)/42188800 by norm_num]
    exact paid_terminal_647
  · change terminalPayment 648 ≤ terminalValue ((point cut hi 1024 648+point cut hi 1024 649)/2)
    have hp : terminalPayment 648 = (335690686585:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 648+point cut hi 1024 649)/2 = (186101263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186101263:ℝ)/42188800) = (2065305:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186101263:ℝ)/42188800)-4 = (17346063:ℝ)/42188800 by norm_num]
    exact paid_terminal_648
  · change terminalPayment 649 ≤ terminalValue ((point cut hi 1024 649+point cut hi 1024 650)/2)
    have hp : terminalPayment 649 = (334974756385:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 649+point cut hi 1024 650)/2 = (186126413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186126413:ℝ)/42188800) = (2064299:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186126413:ℝ)/42188800)-4 = (17371213:ℝ)/42188800 by norm_num]
    exact paid_terminal_649
  · change terminalPayment 650 ≤ terminalValue ((point cut hi 1024 650+point cut hi 1024 651)/2)
    have hp : terminalPayment 650 = (334258022523:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 650+point cut hi 1024 651)/2 = (186151563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186151563:ℝ)/42188800) = (2063293:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186151563:ℝ)/42188800)-4 = (17396363:ℝ)/42188800 by norm_num]
    exact paid_terminal_650
  · change terminalPayment 651 ≤ terminalValue ((point cut hi 1024 651+point cut hi 1024 652)/2)
    have hp : terminalPayment 651 = (333540484001:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 651+point cut hi 1024 652)/2 = (186176713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186176713:ℝ)/42188800) = (2062287:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186176713:ℝ)/42188800)-4 = (17421513:ℝ)/42188800 by norm_num]
    exact paid_terminal_651
  · change terminalPayment 652 ≤ terminalValue ((point cut hi 1024 652+point cut hi 1024 653)/2)
    have hp : terminalPayment 652 = (332822139822:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 652+point cut hi 1024 653)/2 = (186201863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186201863:ℝ)/42188800) = (2061281:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186201863:ℝ)/42188800)-4 = (17446663:ℝ)/42188800 by norm_num]
    exact paid_terminal_652
  · change terminalPayment 653 ≤ terminalValue ((point cut hi 1024 653+point cut hi 1024 654)/2)
    have hp : terminalPayment 653 = (332102988983:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 653+point cut hi 1024 654)/2 = (186227013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186227013:ℝ)/42188800) = (2060275:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186227013:ℝ)/42188800)-4 = (17471813:ℝ)/42188800 by norm_num]
    exact paid_terminal_653
  · change terminalPayment 654 ≤ terminalValue ((point cut hi 1024 654+point cut hi 1024 655)/2)
    have hp : terminalPayment 654 = (331383030482:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 654+point cut hi 1024 655)/2 = (186252163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186252163:ℝ)/42188800) = (2059269:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186252163:ℝ)/42188800)-4 = (17496963:ℝ)/42188800 by norm_num]
    exact paid_terminal_654
  · change terminalPayment 655 ≤ terminalValue ((point cut hi 1024 655+point cut hi 1024 656)/2)
    have hp : terminalPayment 655 = (330662263315:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 655+point cut hi 1024 656)/2 = (186277313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((186277313:ℝ)/42188800) = (2058263:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((186277313:ℝ)/42188800)-4 = (17522113:ℝ)/42188800 by norm_num]
    exact paid_terminal_655
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_040
