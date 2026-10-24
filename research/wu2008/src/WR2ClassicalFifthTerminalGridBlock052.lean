import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints052
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_052 (j : Fin 16) : terminalPayment (16*52+j.val) ≤
    terminalValue ((point cut hi 1024 (16*52+j.val)+point cut hi 1024 (16*52+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 832 ≤ terminalValue ((point cut hi 1024 832+point cut hi 1024 833)/2)
    have hp : terminalPayment 832 = (189325813825:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 832+point cut hi 1024 833)/2 = (190728863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190728863:ℝ)/42188800) = (1880201:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190728863:ℝ)/42188800)-4 = (21973663:ℝ)/42188800 by norm_num]
    exact paid_terminal_832
  · change terminalPayment 833 ≤ terminalValue ((point cut hi 1024 833+point cut hi 1024 834)/2)
    have hp : terminalPayment 833 = (188443313944:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 833+point cut hi 1024 834)/2 = (190754013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190754013:ℝ)/42188800) = (1879195:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190754013:ℝ)/42188800)-4 = (21998813:ℝ)/42188800 by norm_num]
    exact paid_terminal_833
  · change terminalPayment 834 ≤ terminalValue ((point cut hi 1024 834+point cut hi 1024 835)/2)
    have hp : terminalPayment 834 = (187559794486:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 834+point cut hi 1024 835)/2 = (190779163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190779163:ℝ)/42188800) = (1878189:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190779163:ℝ)/42188800)-4 = (22023963:ℝ)/42188800 by norm_num]
    exact paid_terminal_834
  · change terminalPayment 835 ≤ terminalValue ((point cut hi 1024 835+point cut hi 1024 836)/2)
    have hp : terminalPayment 835 = (186675254076:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 835+point cut hi 1024 836)/2 = (190804313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190804313:ℝ)/42188800) = (1877183:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190804313:ℝ)/42188800)-4 = (22049113:ℝ)/42188800 by norm_num]
    exact paid_terminal_835
  · change terminalPayment 836 ≤ terminalValue ((point cut hi 1024 836+point cut hi 1024 837)/2)
    have hp : terminalPayment 836 = (185789691338:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 836+point cut hi 1024 837)/2 = (190829463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190829463:ℝ)/42188800) = (1876177:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190829463:ℝ)/42188800)-4 = (22074263:ℝ)/42188800 by norm_num]
    exact paid_terminal_836
  · change terminalPayment 837 ≤ terminalValue ((point cut hi 1024 837+point cut hi 1024 838)/2)
    have hp : terminalPayment 837 = (184903104890:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 837+point cut hi 1024 838)/2 = (190854613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190854613:ℝ)/42188800) = (1875171:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190854613:ℝ)/42188800)-4 = (22099413:ℝ)/42188800 by norm_num]
    exact paid_terminal_837
  · change terminalPayment 838 ≤ terminalValue ((point cut hi 1024 838+point cut hi 1024 839)/2)
    have hp : terminalPayment 838 = (184015493352:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 838+point cut hi 1024 839)/2 = (190879763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190879763:ℝ)/42188800) = (1874165:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190879763:ℝ)/42188800)-4 = (22124563:ℝ)/42188800 by norm_num]
    exact paid_terminal_838
  · change terminalPayment 839 ≤ terminalValue ((point cut hi 1024 839+point cut hi 1024 840)/2)
    have hp : terminalPayment 839 = (183126855337:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 839+point cut hi 1024 840)/2 = (190904913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190904913:ℝ)/42188800) = (1873159:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190904913:ℝ)/42188800)-4 = (22149713:ℝ)/42188800 by norm_num]
    exact paid_terminal_839
  · change terminalPayment 840 ≤ terminalValue ((point cut hi 1024 840+point cut hi 1024 841)/2)
    have hp : terminalPayment 840 = (182237189460:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 840+point cut hi 1024 841)/2 = (190930063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190930063:ℝ)/42188800) = (1872153:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190930063:ℝ)/42188800)-4 = (22174863:ℝ)/42188800 by norm_num]
    exact paid_terminal_840
  · change terminalPayment 841 ≤ terminalValue ((point cut hi 1024 841+point cut hi 1024 842)/2)
    have hp : terminalPayment 841 = (181346494330:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 841+point cut hi 1024 842)/2 = (190955213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190955213:ℝ)/42188800) = (1871147:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190955213:ℝ)/42188800)-4 = (22200013:ℝ)/42188800 by norm_num]
    exact paid_terminal_841
  · change terminalPayment 842 ≤ terminalValue ((point cut hi 1024 842+point cut hi 1024 843)/2)
    have hp : terminalPayment 842 = (180454768554:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 842+point cut hi 1024 843)/2 = (190980363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190980363:ℝ)/42188800) = (1870141:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190980363:ℝ)/42188800)-4 = (22225163:ℝ)/42188800 by norm_num]
    exact paid_terminal_842
  · change terminalPayment 843 ≤ terminalValue ((point cut hi 1024 843+point cut hi 1024 844)/2)
    have hp : terminalPayment 843 = (179562010740:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 843+point cut hi 1024 844)/2 = (191005513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191005513:ℝ)/42188800) = (1869135:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191005513:ℝ)/42188800)-4 = (22250313:ℝ)/42188800 by norm_num]
    exact paid_terminal_843
  · change terminalPayment 844 ≤ terminalValue ((point cut hi 1024 844+point cut hi 1024 845)/2)
    have hp : terminalPayment 844 = (178668219488:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 844+point cut hi 1024 845)/2 = (191030663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191030663:ℝ)/42188800) = (1868129:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191030663:ℝ)/42188800)-4 = (22275463:ℝ)/42188800 by norm_num]
    exact paid_terminal_844
  · change terminalPayment 845 ≤ terminalValue ((point cut hi 1024 845+point cut hi 1024 846)/2)
    have hp : terminalPayment 845 = (177773393400:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 845+point cut hi 1024 846)/2 = (191055813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191055813:ℝ)/42188800) = (1867123:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191055813:ℝ)/42188800)-4 = (22300613:ℝ)/42188800 by norm_num]
    exact paid_terminal_845
  · change terminalPayment 846 ≤ terminalValue ((point cut hi 1024 846+point cut hi 1024 847)/2)
    have hp : terminalPayment 846 = (176877531073:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 846+point cut hi 1024 847)/2 = (191080963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191080963:ℝ)/42188800) = (1866117:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191080963:ℝ)/42188800)-4 = (22325763:ℝ)/42188800 by norm_num]
    exact paid_terminal_846
  · change terminalPayment 847 ≤ terminalValue ((point cut hi 1024 847+point cut hi 1024 848)/2)
    have hp : terminalPayment 847 = (175980631102:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 847+point cut hi 1024 848)/2 = (191106113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191106113:ℝ)/42188800) = (1865111:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191106113:ℝ)/42188800)-4 = (22350913:ℝ)/42188800 by norm_num]
    exact paid_terminal_847
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_052
