import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints007
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_007 (j : Fin 16) : initialPayment (16*7+j.val) ≤
    initialValue ((point lo 4 1024 (16*7+j.val)+point lo 4 1024 (16*7+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 112 ≤ initialValue ((point lo 4 1024 112+point lo 4 1024 113)/2)
    have hp : initialPayment 112 = (44743669609:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 112+point lo 4 1024 113)/2 = (146753413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146753413:ℝ)/42188800) = (2717696:ℝ)/2609075 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_112
  · change initialPayment 113 ≤ initialValue ((point lo 4 1024 113+point lo 4 1024 114)/2)
    have hp : initialPayment 113 = (45161929617:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 113+point lo 4 1024 114)/2 = (146777551:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146777551:ℝ)/42188800) = (67942400:ℝ)/65202737 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_113
  · change initialPayment 114 ≤ initialValue ((point lo 4 1024 114+point lo 4 1024 115)/2)
    have hp : initialPayment 114 = (45580560657:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 114+point lo 4 1024 115)/2 = (146801689:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146801689:ℝ)/42188800) = (67942400:ℝ)/65178599 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_114
  · change initialPayment 115 ≤ initialValue ((point lo 4 1024 115+point lo 4 1024 116)/2)
    have hp : initialPayment 115 = (45999562978:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 115+point lo 4 1024 116)/2 = (146825827:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146825827:ℝ)/42188800) = (67942400:ℝ)/65154461 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_115
  · change initialPayment 116 ≤ initialValue ((point lo 4 1024 116+point lo 4 1024 117)/2)
    have hp : initialPayment 116 = (46418936829:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 116+point lo 4 1024 117)/2 = (29369993:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29369993:ℝ)/8437760) = (67942400:ℝ)/65130323 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_116
  · change initialPayment 117 ≤ initialValue ((point lo 4 1024 117+point lo 4 1024 118)/2)
    have hp : initialPayment 117 = (46838682462:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 117+point lo 4 1024 118)/2 = (146874103:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146874103:ℝ)/42188800) = (13588480:ℝ)/13021237 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_117
  · change initialPayment 118 ≤ initialValue ((point lo 4 1024 118+point lo 4 1024 119)/2)
    have hp : initialPayment 118 = (47258800126:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 118+point lo 4 1024 119)/2 = (146898241:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146898241:ℝ)/42188800) = (67942400:ℝ)/65082047 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_118
  · change initialPayment 119 ≤ initialValue ((point lo 4 1024 119+point lo 4 1024 120)/2)
    have hp : initialPayment 119 = (47679290074:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 119+point lo 4 1024 120)/2 = (146922379:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146922379:ℝ)/42188800) = (67942400:ℝ)/65057909 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_119
  · change initialPayment 120 ≤ initialValue ((point lo 4 1024 120+point lo 4 1024 121)/2)
    have hp : initialPayment 120 = (48100152556:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 120+point lo 4 1024 121)/2 = (146946517:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146946517:ℝ)/42188800) = (67942400:ℝ)/65033771 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_120
  · change initialPayment 121 ≤ initialValue ((point lo 4 1024 121+point lo 4 1024 122)/2)
    have hp : initialPayment 121 = (48521387824:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 121+point lo 4 1024 122)/2 = (29394131:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29394131:ℝ)/8437760) = (67942400:ℝ)/65009633 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_121
  · change initialPayment 122 ≤ initialValue ((point lo 4 1024 122+point lo 4 1024 123)/2)
    have hp : initialPayment 122 = (48942996130:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 122+point lo 4 1024 123)/2 = (146994793:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146994793:ℝ)/42188800) = (13588480:ℝ)/12997099 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_122
  · change initialPayment 123 ≤ initialValue ((point lo 4 1024 123+point lo 4 1024 124)/2)
    have hp : initialPayment 123 = (49364977727:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 123+point lo 4 1024 124)/2 = (147018931:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147018931:ℝ)/42188800) = (67942400:ℝ)/64961357 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_123
  · change initialPayment 124 ≤ initialValue ((point lo 4 1024 124+point lo 4 1024 125)/2)
    have hp : initialPayment 124 = (49787332868:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 124+point lo 4 1024 125)/2 = (147043069:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147043069:ℝ)/42188800) = (67942400:ℝ)/64937219 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_124
  · change initialPayment 125 ≤ initialValue ((point lo 4 1024 125+point lo 4 1024 126)/2)
    have hp : initialPayment 125 = (50210061806:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 125+point lo 4 1024 126)/2 = (147067207:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147067207:ℝ)/42188800) = (67942400:ℝ)/64913081 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_125
  · change initialPayment 126 ≤ initialValue ((point lo 4 1024 126+point lo 4 1024 127)/2)
    have hp : initialPayment 126 = (50633164795:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 126+point lo 4 1024 127)/2 = (29418269:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29418269:ℝ)/8437760) = (67942400:ℝ)/64888943 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_126
  · change initialPayment 127 ≤ initialValue ((point lo 4 1024 127+point lo 4 1024 128)/2)
    have hp : initialPayment 127 = (51056642088:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 127+point lo 4 1024 128)/2 = (147115483:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147115483:ℝ)/42188800) = (13588480:ℝ)/12972961 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_127
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_007
