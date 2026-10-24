import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints051
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_051 (j : Fin 16) : terminalPayment (16*51+j.val) ≤
    terminalValue ((point cut hi 1024 (16*51+j.val)+point cut hi 1024 (16*51+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 816 ≤ terminalValue ((point cut hi 1024 816+point cut hi 1024 817)/2)
    have hp : terminalPayment 816 = (203308261845:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 816+point cut hi 1024 817)/2 = (190326463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190326463:ℝ)/42188800) = (1896297:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190326463:ℝ)/42188800)-4 = (21571263:ℝ)/42188800 by norm_num]
    exact paid_terminal_816
  · change terminalPayment 817 ≤ terminalValue ((point cut hi 1024 817+point cut hi 1024 818)/2)
    have hp : terminalPayment 817 = (202441890209:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 817+point cut hi 1024 818)/2 = (190351613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190351613:ℝ)/42188800) = (1895291:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190351613:ℝ)/42188800)-4 = (21596413:ℝ)/42188800 by norm_num]
    exact paid_terminal_817
  · change terminalPayment 818 ≤ terminalValue ((point cut hi 1024 818+point cut hi 1024 819)/2)
    have hp : terminalPayment 818 = (201574520663:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 818+point cut hi 1024 819)/2 = (190376763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190376763:ℝ)/42188800) = (1894285:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190376763:ℝ)/42188800)-4 = (21621563:ℝ)/42188800 by norm_num]
    exact paid_terminal_818
  · change terminalPayment 819 ≤ terminalValue ((point cut hi 1024 819+point cut hi 1024 820)/2)
    have hp : terminalPayment 819 = (200706151871:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 819+point cut hi 1024 820)/2 = (190401913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190401913:ℝ)/42188800) = (1893279:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190401913:ℝ)/42188800)-4 = (21646713:ℝ)/42188800 by norm_num]
    exact paid_terminal_819
  · change terminalPayment 820 ≤ terminalValue ((point cut hi 1024 820+point cut hi 1024 821)/2)
    have hp : terminalPayment 820 = (199836782493:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 820+point cut hi 1024 821)/2 = (190427063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190427063:ℝ)/42188800) = (1892273:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190427063:ℝ)/42188800)-4 = (21671863:ℝ)/42188800 by norm_num]
    exact paid_terminal_820
  · change terminalPayment 821 ≤ terminalValue ((point cut hi 1024 821+point cut hi 1024 822)/2)
    have hp : terminalPayment 821 = (198966411188:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 821+point cut hi 1024 822)/2 = (190452213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190452213:ℝ)/42188800) = (1891267:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190452213:ℝ)/42188800)-4 = (21697013:ℝ)/42188800 by norm_num]
    exact paid_terminal_821
  · change terminalPayment 822 ≤ terminalValue ((point cut hi 1024 822+point cut hi 1024 823)/2)
    have hp : terminalPayment 822 = (198095036615:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 822+point cut hi 1024 823)/2 = (190477363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190477363:ℝ)/42188800) = (1890261:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190477363:ℝ)/42188800)-4 = (21722163:ℝ)/42188800 by norm_num]
    exact paid_terminal_822
  · change terminalPayment 823 ≤ terminalValue ((point cut hi 1024 823+point cut hi 1024 824)/2)
    have hp : terminalPayment 823 = (197222657426:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 823+point cut hi 1024 824)/2 = (190502513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190502513:ℝ)/42188800) = (1889255:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190502513:ℝ)/42188800)-4 = (21747313:ℝ)/42188800 by norm_num]
    exact paid_terminal_823
  · change terminalPayment 824 ≤ terminalValue ((point cut hi 1024 824+point cut hi 1024 825)/2)
    have hp : terminalPayment 824 = (196349272274:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 824+point cut hi 1024 825)/2 = (190527663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190527663:ℝ)/42188800) = (1888249:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190527663:ℝ)/42188800)-4 = (21772463:ℝ)/42188800 by norm_num]
    exact paid_terminal_824
  · change terminalPayment 825 ≤ terminalValue ((point cut hi 1024 825+point cut hi 1024 826)/2)
    have hp : terminalPayment 825 = (195474879809:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 825+point cut hi 1024 826)/2 = (190552813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190552813:ℝ)/42188800) = (1887243:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190552813:ℝ)/42188800)-4 = (21797613:ℝ)/42188800 by norm_num]
    exact paid_terminal_825
  · change terminalPayment 826 ≤ terminalValue ((point cut hi 1024 826+point cut hi 1024 827)/2)
    have hp : terminalPayment 826 = (194599478677:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 826+point cut hi 1024 827)/2 = (190577963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190577963:ℝ)/42188800) = (1886237:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190577963:ℝ)/42188800)-4 = (21822763:ℝ)/42188800 by norm_num]
    exact paid_terminal_826
  · change terminalPayment 827 ≤ terminalValue ((point cut hi 1024 827+point cut hi 1024 828)/2)
    have hp : terminalPayment 827 = (193723067523:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 827+point cut hi 1024 828)/2 = (190603113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190603113:ℝ)/42188800) = (1885231:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190603113:ℝ)/42188800)-4 = (21847913:ℝ)/42188800 by norm_num]
    exact paid_terminal_827
  · change terminalPayment 828 ≤ terminalValue ((point cut hi 1024 828+point cut hi 1024 829)/2)
    have hp : terminalPayment 828 = (192845644990:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 828+point cut hi 1024 829)/2 = (190628263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190628263:ℝ)/42188800) = (1884225:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190628263:ℝ)/42188800)-4 = (21873063:ℝ)/42188800 by norm_num]
    exact paid_terminal_828
  · change terminalPayment 829 ≤ terminalValue ((point cut hi 1024 829+point cut hi 1024 830)/2)
    have hp : terminalPayment 829 = (191967209718:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 829+point cut hi 1024 830)/2 = (190653413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190653413:ℝ)/42188800) = (1883219:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190653413:ℝ)/42188800)-4 = (21898213:ℝ)/42188800 by norm_num]
    exact paid_terminal_829
  · change terminalPayment 830 ≤ terminalValue ((point cut hi 1024 830+point cut hi 1024 831)/2)
    have hp : terminalPayment 830 = (191087760343:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 830+point cut hi 1024 831)/2 = (190678563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190678563:ℝ)/42188800) = (1882213:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190678563:ℝ)/42188800)-4 = (21923363:ℝ)/42188800 by norm_num]
    exact paid_terminal_830
  · change terminalPayment 831 ≤ terminalValue ((point cut hi 1024 831+point cut hi 1024 832)/2)
    have hp : terminalPayment 831 = (190207295501:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 831+point cut hi 1024 832)/2 = (190703713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190703713:ℝ)/42188800) = (1881207:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190703713:ℝ)/42188800)-4 = (21948513:ℝ)/42188800 by norm_num]
    exact paid_terminal_831
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_051
