import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints008
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_008 (j : Fin 16) : initialPayment (16*8+j.val) ≤
    initialValue ((point lo 4 1024 (16*8+j.val)+point lo 4 1024 (16*8+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 128 ≤ initialValue ((point lo 4 1024 128+point lo 4 1024 129)/2)
    have hp : initialPayment 128 = (51480493941:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 128+point lo 4 1024 129)/2 = (147139621:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147139621:ℝ)/42188800) = (67942400:ℝ)/64840667 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_128
  · change initialPayment 129 ≤ initialValue ((point lo 4 1024 129+point lo 4 1024 130)/2)
    have hp : initialPayment 129 = (51904720609:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 129+point lo 4 1024 130)/2 = (147163759:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147163759:ℝ)/42188800) = (67942400:ℝ)/64816529 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_129
  · change initialPayment 130 ≤ initialValue ((point lo 4 1024 130+point lo 4 1024 131)/2)
    have hp : initialPayment 130 = (52329322346:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 130+point lo 4 1024 131)/2 = (147187897:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147187897:ℝ)/42188800) = (67942400:ℝ)/64792391 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_130
  · change initialPayment 131 ≤ initialValue ((point lo 4 1024 131+point lo 4 1024 132)/2)
    have hp : initialPayment 131 = (52754299408:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 131+point lo 4 1024 132)/2 = (29442407:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29442407:ℝ)/8437760) = (67942400:ℝ)/64768253 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_131
  · change initialPayment 132 ≤ initialValue ((point lo 4 1024 132+point lo 4 1024 133)/2)
    have hp : initialPayment 132 = (53179652051:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 132+point lo 4 1024 133)/2 = (147236173:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147236173:ℝ)/42188800) = (13588480:ℝ)/12948823 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_132
  · change initialPayment 133 ≤ initialValue ((point lo 4 1024 133+point lo 4 1024 134)/2)
    have hp : initialPayment 133 = (53605380531:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 133+point lo 4 1024 134)/2 = (147260311:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147260311:ℝ)/42188800) = (67942400:ℝ)/64719977 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_133
  · change initialPayment 134 ≤ initialValue ((point lo 4 1024 134+point lo 4 1024 135)/2)
    have hp : initialPayment 134 = (54031485106:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 134+point lo 4 1024 135)/2 = (147284449:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147284449:ℝ)/42188800) = (67942400:ℝ)/64695839 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_134
  · change initialPayment 135 ≤ initialValue ((point lo 4 1024 135+point lo 4 1024 136)/2)
    have hp : initialPayment 135 = (54457966032:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 135+point lo 4 1024 136)/2 = (147308587:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147308587:ℝ)/42188800) = (67942400:ℝ)/64671701 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_135
  · change initialPayment 136 ≤ initialValue ((point lo 4 1024 136+point lo 4 1024 137)/2)
    have hp : initialPayment 136 = (54884823567:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 136+point lo 4 1024 137)/2 = (5893309:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((5893309:ℝ)/1687552) = (67942400:ℝ)/64647563 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_136
  · change initialPayment 137 ≤ initialValue ((point lo 4 1024 137+point lo 4 1024 138)/2)
    have hp : initialPayment 137 = (55312057969:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 137+point lo 4 1024 138)/2 = (147356863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147356863:ℝ)/42188800) = (2717696:ℝ)/2584937 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_137
  · change initialPayment 138 ≤ initialValue ((point lo 4 1024 138+point lo 4 1024 139)/2)
    have hp : initialPayment 138 = (55739669497:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 138+point lo 4 1024 139)/2 = (147381001:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147381001:ℝ)/42188800) = (67942400:ℝ)/64599287 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_138
  · change initialPayment 139 ≤ initialValue ((point lo 4 1024 139+point lo 4 1024 140)/2)
    have hp : initialPayment 139 = (56167658408:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 139+point lo 4 1024 140)/2 = (147405139:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147405139:ℝ)/42188800) = (67942400:ℝ)/64575149 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_139
  · change initialPayment 140 ≤ initialValue ((point lo 4 1024 140+point lo 4 1024 141)/2)
    have hp : initialPayment 140 = (56596024962:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 140+point lo 4 1024 141)/2 = (147429277:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147429277:ℝ)/42188800) = (67942400:ℝ)/64551011 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_140
  · change initialPayment 141 ≤ initialValue ((point lo 4 1024 141+point lo 4 1024 142)/2)
    have hp : initialPayment 141 = (57024769419:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 141+point lo 4 1024 142)/2 = (29490683:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29490683:ℝ)/8437760) = (67942400:ℝ)/64526873 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_141
  · change initialPayment 142 ≤ initialValue ((point lo 4 1024 142+point lo 4 1024 143)/2)
    have hp : initialPayment 142 = (57453892038:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 142+point lo 4 1024 143)/2 = (147477553:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147477553:ℝ)/42188800) = (13588480:ℝ)/12900547 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_142
  · change initialPayment 143 ≤ initialValue ((point lo 4 1024 143+point lo 4 1024 144)/2)
    have hp : initialPayment 143 = (57883393080:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 143+point lo 4 1024 144)/2 = (147501691:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147501691:ℝ)/42188800) = (67942400:ℝ)/64478597 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_143
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_008
