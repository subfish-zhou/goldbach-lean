import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints009
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_009 (j : Fin 16) : initialPayment (16*9+j.val) ≤
    initialValue ((point lo 4 1024 (16*9+j.val)+point lo 4 1024 (16*9+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 144 ≤ initialValue ((point lo 4 1024 144+point lo 4 1024 145)/2)
    have hp : initialPayment 144 = (58313272806:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 144+point lo 4 1024 145)/2 = (147525829:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147525829:ℝ)/42188800) = (67942400:ℝ)/64454459 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_144
  · change initialPayment 145 ≤ initialValue ((point lo 4 1024 145+point lo 4 1024 146)/2)
    have hp : initialPayment 145 = (58743531475:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 145+point lo 4 1024 146)/2 = (147549967:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147549967:ℝ)/42188800) = (67942400:ℝ)/64430321 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_145
  · change initialPayment 146 ≤ initialValue ((point lo 4 1024 146+point lo 4 1024 147)/2)
    have hp : initialPayment 146 = (59174169351:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 146+point lo 4 1024 147)/2 = (29514821:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29514821:ℝ)/8437760) = (67942400:ℝ)/64406183 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_146
  · change initialPayment 147 ≤ initialValue ((point lo 4 1024 147+point lo 4 1024 148)/2)
    have hp : initialPayment 147 = (59605186694:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 147+point lo 4 1024 148)/2 = (147598243:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147598243:ℝ)/42188800) = (13588480:ℝ)/12876409 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_147
  · change initialPayment 148 ≤ initialValue ((point lo 4 1024 148+point lo 4 1024 149)/2)
    have hp : initialPayment 148 = (60036583767:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 148+point lo 4 1024 149)/2 = (1433227:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((1433227:ℝ)/409600) = (67942400:ℝ)/64357907 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_148
  · change initialPayment 149 ≤ initialValue ((point lo 4 1024 149+point lo 4 1024 150)/2)
    have hp : initialPayment 149 = (60468360832:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 149+point lo 4 1024 150)/2 = (147646519:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147646519:ℝ)/42188800) = (67942400:ℝ)/64333769 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_149
  · change initialPayment 150 ≤ initialValue ((point lo 4 1024 150+point lo 4 1024 151)/2)
    have hp : initialPayment 150 = (60900518153:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 150+point lo 4 1024 151)/2 = (147670657:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147670657:ℝ)/42188800) = (67942400:ℝ)/64309631 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_150
  · change initialPayment 151 ≤ initialValue ((point lo 4 1024 151+point lo 4 1024 152)/2)
    have hp : initialPayment 151 = (61333055993:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 151+point lo 4 1024 152)/2 = (29538959:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29538959:ℝ)/8437760) = (67942400:ℝ)/64285493 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_151
  · change initialPayment 152 ≤ initialValue ((point lo 4 1024 152+point lo 4 1024 153)/2)
    have hp : initialPayment 152 = (61765974615:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 152+point lo 4 1024 153)/2 = (147718933:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147718933:ℝ)/42188800) = (13588480:ℝ)/12852271 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_152
  · change initialPayment 153 ≤ initialValue ((point lo 4 1024 153+point lo 4 1024 154)/2)
    have hp : initialPayment 153 = (62199274285:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 153+point lo 4 1024 154)/2 = (147743071:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147743071:ℝ)/42188800) = (67942400:ℝ)/64237217 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_153
  · change initialPayment 154 ≤ initialValue ((point lo 4 1024 154+point lo 4 1024 155)/2)
    have hp : initialPayment 154 = (62632955266:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 154+point lo 4 1024 155)/2 = (147767209:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147767209:ℝ)/42188800) = (67942400:ℝ)/64213079 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_154
  · change initialPayment 155 ≤ initialValue ((point lo 4 1024 155+point lo 4 1024 156)/2)
    have hp : initialPayment 155 = (63067017823:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 155+point lo 4 1024 156)/2 = (147791347:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147791347:ℝ)/42188800) = (67942400:ℝ)/64188941 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_155
  · change initialPayment 156 ≤ initialValue ((point lo 4 1024 156+point lo 4 1024 157)/2)
    have hp : initialPayment 156 = (63501462222:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 156+point lo 4 1024 157)/2 = (29563097:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29563097:ℝ)/8437760) = (67942400:ℝ)/64164803 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_156
  · change initialPayment 157 ≤ initialValue ((point lo 4 1024 157+point lo 4 1024 158)/2)
    have hp : initialPayment 157 = (63936288729:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 157+point lo 4 1024 158)/2 = (147839623:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147839623:ℝ)/42188800) = (13588480:ℝ)/12828133 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_157
  · change initialPayment 158 ≤ initialValue ((point lo 4 1024 158+point lo 4 1024 159)/2)
    have hp : initialPayment 158 = (64371497610:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 158+point lo 4 1024 159)/2 = (147863761:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147863761:ℝ)/42188800) = (67942400:ℝ)/64116527 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_158
  · change initialPayment 159 ≤ initialValue ((point lo 4 1024 159+point lo 4 1024 160)/2)
    have hp : initialPayment 159 = (64807089131:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 159+point lo 4 1024 160)/2 = (147887899:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((147887899:ℝ)/42188800) = (67942400:ℝ)/64092389 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_159
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_009
