import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints060
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_060 (j : Fin 16) : terminalPayment (16*60+j.val) ≤
    terminalValue ((point cut hi 1024 (16*60+j.val)+point cut hi 1024 (16*60+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 960 ≤ terminalValue ((point cut hi 1024 960+point cut hi 1024 961)/2)
    have hp : terminalPayment 960 = (67581593644:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 960+point cut hi 1024 961)/2 = (193948063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193948063:ℝ)/42188800) = (1751433:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193948063:ℝ)/42188800)-4 = (25192863:ℝ)/42188800 by norm_num]
    exact paid_terminal_960
  · change terminalPayment 961 ≤ terminalValue ((point cut hi 1024 961+point cut hi 1024 962)/2)
    have hp : terminalPayment 961 = (66556511403:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 961+point cut hi 1024 962)/2 = (193973213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193973213:ℝ)/42188800) = (1750427:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193973213:ℝ)/42188800)-4 = (25218013:ℝ)/42188800 by norm_num]
    exact paid_terminal_961
  · change terminalPayment 962 ≤ terminalValue ((point cut hi 1024 962+point cut hi 1024 963)/2)
    have hp : terminalPayment 962 = (65530211607:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 962+point cut hi 1024 963)/2 = (193998363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193998363:ℝ)/42188800) = (1749421:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193998363:ℝ)/42188800)-4 = (25243163:ℝ)/42188800 by norm_num]
    exact paid_terminal_962
  · change terminalPayment 963 ≤ terminalValue ((point cut hi 1024 963+point cut hi 1024 964)/2)
    have hp : terminalPayment 963 = (64502692518:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 963+point cut hi 1024 964)/2 = (194023513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194023513:ℝ)/42188800) = (1748415:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194023513:ℝ)/42188800)-4 = (25268313:ℝ)/42188800 by norm_num]
    exact paid_terminal_963
  · change terminalPayment 964 ≤ terminalValue ((point cut hi 1024 964+point cut hi 1024 965)/2)
    have hp : terminalPayment 964 = (63473952394:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 964+point cut hi 1024 965)/2 = (194048663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194048663:ℝ)/42188800) = (1747409:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194048663:ℝ)/42188800)-4 = (25293463:ℝ)/42188800 by norm_num]
    exact paid_terminal_964
  · change terminalPayment 965 ≤ terminalValue ((point cut hi 1024 965+point cut hi 1024 966)/2)
    have hp : terminalPayment 965 = (62443989491:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 965+point cut hi 1024 966)/2 = (194073813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194073813:ℝ)/42188800) = (1746403:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194073813:ℝ)/42188800)-4 = (25318613:ℝ)/42188800 by norm_num]
    exact paid_terminal_965
  · change terminalPayment 966 ≤ terminalValue ((point cut hi 1024 966+point cut hi 1024 967)/2)
    have hp : terminalPayment 966 = (61412802059:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 966+point cut hi 1024 967)/2 = (194098963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194098963:ℝ)/42188800) = (1745397:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194098963:ℝ)/42188800)-4 = (25343763:ℝ)/42188800 by norm_num]
    exact paid_terminal_966
  · change terminalPayment 967 ≤ terminalValue ((point cut hi 1024 967+point cut hi 1024 968)/2)
    have hp : terminalPayment 967 = (60380388348:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 967+point cut hi 1024 968)/2 = (194124113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194124113:ℝ)/42188800) = (1744391:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194124113:ℝ)/42188800)-4 = (25368913:ℝ)/42188800 by norm_num]
    exact paid_terminal_967
  · change terminalPayment 968 ≤ terminalValue ((point cut hi 1024 968+point cut hi 1024 969)/2)
    have hp : terminalPayment 968 = (59346746603:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 968+point cut hi 1024 969)/2 = (194149263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194149263:ℝ)/42188800) = (1743385:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194149263:ℝ)/42188800)-4 = (25394063:ℝ)/42188800 by norm_num]
    exact paid_terminal_968
  · change terminalPayment 969 ≤ terminalValue ((point cut hi 1024 969+point cut hi 1024 970)/2)
    have hp : terminalPayment 969 = (58311875065:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 969+point cut hi 1024 970)/2 = (194174413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194174413:ℝ)/42188800) = (1742379:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194174413:ℝ)/42188800)-4 = (25419213:ℝ)/42188800 by norm_num]
    exact paid_terminal_969
  · change terminalPayment 970 ≤ terminalValue ((point cut hi 1024 970+point cut hi 1024 971)/2)
    have hp : terminalPayment 970 = (57275771972:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 970+point cut hi 1024 971)/2 = (194199563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194199563:ℝ)/42188800) = (1741373:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194199563:ℝ)/42188800)-4 = (25444363:ℝ)/42188800 by norm_num]
    exact paid_terminal_970
  · change terminalPayment 971 ≤ terminalValue ((point cut hi 1024 971+point cut hi 1024 972)/2)
    have hp : terminalPayment 971 = (56238435561:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 971+point cut hi 1024 972)/2 = (194224713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194224713:ℝ)/42188800) = (1740367:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194224713:ℝ)/42188800)-4 = (25469513:ℝ)/42188800 by norm_num]
    exact paid_terminal_971
  · change terminalPayment 972 ≤ terminalValue ((point cut hi 1024 972+point cut hi 1024 973)/2)
    have hp : terminalPayment 972 = (55199864063:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 972+point cut hi 1024 973)/2 = (1885921:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((1885921:ℝ)/409600) = (16887:ℝ)/16384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((1885921:ℝ)/409600)-4 = (247521:ℝ)/409600 by norm_num]
    exact paid_terminal_972
  · change terminalPayment 973 ≤ terminalValue ((point cut hi 1024 973+point cut hi 1024 974)/2)
    have hp : terminalPayment 973 = (54160055706:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 973+point cut hi 1024 974)/2 = (194275013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194275013:ℝ)/42188800) = (1738355:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194275013:ℝ)/42188800)-4 = (25519813:ℝ)/42188800 by norm_num]
    exact paid_terminal_973
  · change terminalPayment 974 ≤ terminalValue ((point cut hi 1024 974+point cut hi 1024 975)/2)
    have hp : terminalPayment 974 = (53119008716:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 974+point cut hi 1024 975)/2 = (194300163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194300163:ℝ)/42188800) = (1737349:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194300163:ℝ)/42188800)-4 = (25544963:ℝ)/42188800 by norm_num]
    exact paid_terminal_974
  · change terminalPayment 975 ≤ terminalValue ((point cut hi 1024 975+point cut hi 1024 976)/2)
    have hp : terminalPayment 975 = (52076721315:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 975+point cut hi 1024 976)/2 = (194325313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((194325313:ℝ)/42188800) = (1736343:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((194325313:ℝ)/42188800)-4 = (25570113:ℝ)/42188800 by norm_num]
    exact paid_terminal_975
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_060
