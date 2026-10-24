import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints055
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_055 (j : Fin 16) : terminalPayment (16*55+j.val) ≤
    terminalValue ((point cut hi 1024 (16*55+j.val)+point cut hi 1024 (16*55+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 880 ≤ terminalValue ((point cut hi 1024 880+point cut hi 1024 881)/2)
    have hp : terminalPayment 880 = (145791468598:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 880+point cut hi 1024 881)/2 = (191936063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191936063:ℝ)/42188800) = (1831913:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191936063:ℝ)/42188800)-4 = (23180863:ℝ)/42188800 by norm_num]
    exact paid_terminal_880
  · change terminalPayment 881 ≤ terminalValue ((point cut hi 1024 881+point cut hi 1024 882)/2)
    have hp : terminalPayment 881 = (144858434510:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 881+point cut hi 1024 882)/2 = (191961213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191961213:ℝ)/42188800) = (1830907:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191961213:ℝ)/42188800)-4 = (23206013:ℝ)/42188800 by norm_num]
    exact paid_terminal_881
  · change terminalPayment 882 ≤ terminalValue ((point cut hi 1024 882+point cut hi 1024 883)/2)
    have hp : terminalPayment 882 = (143924311978:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 882+point cut hi 1024 883)/2 = (191986363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191986363:ℝ)/42188800) = (1829901:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191986363:ℝ)/42188800)-4 = (23231163:ℝ)/42188800 by norm_num]
    exact paid_terminal_882
  · change terminalPayment 883 ≤ terminalValue ((point cut hi 1024 883+point cut hi 1024 884)/2)
    have hp : terminalPayment 883 = (142989099501:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 883+point cut hi 1024 884)/2 = (192011513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192011513:ℝ)/42188800) = (1828895:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192011513:ℝ)/42188800)-4 = (23256313:ℝ)/42188800 by norm_num]
    exact paid_terminal_883
  · change terminalPayment 884 ≤ terminalValue ((point cut hi 1024 884+point cut hi 1024 885)/2)
    have hp : terminalPayment 884 = (142052795579:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 884+point cut hi 1024 885)/2 = (192036663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192036663:ℝ)/42188800) = (1827889:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192036663:ℝ)/42188800)-4 = (23281463:ℝ)/42188800 by norm_num]
    exact paid_terminal_884
  · change terminalPayment 885 ≤ terminalValue ((point cut hi 1024 885+point cut hi 1024 886)/2)
    have hp : terminalPayment 885 = (141115398706:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 885+point cut hi 1024 886)/2 = (192061813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192061813:ℝ)/42188800) = (1826883:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192061813:ℝ)/42188800)-4 = (23306613:ℝ)/42188800 by norm_num]
    exact paid_terminal_885
  · change terminalPayment 886 ≤ terminalValue ((point cut hi 1024 886+point cut hi 1024 887)/2)
    have hp : terminalPayment 886 = (140176907374:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 886+point cut hi 1024 887)/2 = (192086963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192086963:ℝ)/42188800) = (1825877:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192086963:ℝ)/42188800)-4 = (23331763:ℝ)/42188800 by norm_num]
    exact paid_terminal_886
  · change terminalPayment 887 ≤ terminalValue ((point cut hi 1024 887+point cut hi 1024 888)/2)
    have hp : terminalPayment 887 = (139237320073:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 887+point cut hi 1024 888)/2 = (192112113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192112113:ℝ)/42188800) = (1824871:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192112113:ℝ)/42188800)-4 = (23356913:ℝ)/42188800 by norm_num]
    exact paid_terminal_887
  · change terminalPayment 888 ≤ terminalValue ((point cut hi 1024 888+point cut hi 1024 889)/2)
    have hp : terminalPayment 888 = (138296635291:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 888+point cut hi 1024 889)/2 = (192137263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192137263:ℝ)/42188800) = (1823865:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192137263:ℝ)/42188800)-4 = (23382063:ℝ)/42188800 by norm_num]
    exact paid_terminal_888
  · change terminalPayment 889 ≤ terminalValue ((point cut hi 1024 889+point cut hi 1024 890)/2)
    have hp : terminalPayment 889 = (137354851511:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 889+point cut hi 1024 890)/2 = (192162413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192162413:ℝ)/42188800) = (1822859:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192162413:ℝ)/42188800)-4 = (23407213:ℝ)/42188800 by norm_num]
    exact paid_terminal_889
  · change terminalPayment 890 ≤ terminalValue ((point cut hi 1024 890+point cut hi 1024 891)/2)
    have hp : terminalPayment 890 = (136411967214:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 890+point cut hi 1024 891)/2 = (192187563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192187563:ℝ)/42188800) = (1821853:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192187563:ℝ)/42188800)-4 = (23432363:ℝ)/42188800 by norm_num]
    exact paid_terminal_890
  · change terminalPayment 891 ≤ terminalValue ((point cut hi 1024 891+point cut hi 1024 892)/2)
    have hp : terminalPayment 891 = (135467980879:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 891+point cut hi 1024 892)/2 = (192212713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192212713:ℝ)/42188800) = (1820847:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192212713:ℝ)/42188800)-4 = (23457513:ℝ)/42188800 by norm_num]
    exact paid_terminal_891
  · change terminalPayment 892 ≤ terminalValue ((point cut hi 1024 892+point cut hi 1024 893)/2)
    have hp : terminalPayment 892 = (134522890982:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 892+point cut hi 1024 893)/2 = (192237863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192237863:ℝ)/42188800) = (1819841:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192237863:ℝ)/42188800)-4 = (23482663:ℝ)/42188800 by norm_num]
    exact paid_terminal_892
  · change terminalPayment 893 ≤ terminalValue ((point cut hi 1024 893+point cut hi 1024 894)/2)
    have hp : terminalPayment 893 = (133576695996:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 893+point cut hi 1024 894)/2 = (192263013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192263013:ℝ)/42188800) = (1818835:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192263013:ℝ)/42188800)-4 = (23507813:ℝ)/42188800 by norm_num]
    exact paid_terminal_893
  · change terminalPayment 894 ≤ terminalValue ((point cut hi 1024 894+point cut hi 1024 895)/2)
    have hp : terminalPayment 894 = (132629394392:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 894+point cut hi 1024 895)/2 = (192288163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192288163:ℝ)/42188800) = (1817829:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192288163:ℝ)/42188800)-4 = (23532963:ℝ)/42188800 by norm_num]
    exact paid_terminal_894
  · change terminalPayment 895 ≤ terminalValue ((point cut hi 1024 895+point cut hi 1024 896)/2)
    have hp : terminalPayment 895 = (131680984635:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 895+point cut hi 1024 896)/2 = (192313313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192313313:ℝ)/42188800) = (1816823:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192313313:ℝ)/42188800)-4 = (23558113:ℝ)/42188800 by norm_num]
    exact paid_terminal_895
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_055
