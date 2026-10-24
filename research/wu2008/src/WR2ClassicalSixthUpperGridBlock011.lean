import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints011
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_011 (j : Fin 16) : upperPayment (16*11+j.val) ≤
    upperValue ((point split endpoint 4096 (16*11+j.val)+point split endpoint 4096 (16*11+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 176 ≤ upperValue ((point split endpoint 4096 176+point split endpoint 4096 177)/2)
    have hp : upperPayment 176 = (414461364457:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 176+point split endpoint 4096 177)/2 = (580590527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580590527:ℝ)/168755200)*ClassicalSixthBranch.v ((580590527:ℝ)/168755200)/ClassicalSixthBranch.r = (158407307198225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_176
  · change upperPayment 177 ≤ upperValue ((point split endpoint 4096 177+point split endpoint 4096 178)/2)
    have hp : upperPayment 177 = (414403859161:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 177+point split endpoint 4096 178)/2 = (580615677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580615677:ℝ)/168755200)*ClassicalSixthBranch.v ((580615677:ℝ)/168755200)/ClassicalSixthBranch.r = (158381648142105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_177
  · change upperPayment 178 ≤ upperValue ((point split endpoint 4096 178+point split endpoint 4096 179)/2)
    have hp : upperPayment 178 = (414346334227:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 178+point split endpoint 4096 179)/2 = (580640827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580640827:ℝ)/168755200)*ClassicalSixthBranch.v ((580640827:ℝ)/168755200)/ClassicalSixthBranch.r = (158355991110057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_178
  · change upperPayment 179 ≤ upperValue ((point split endpoint 4096 179+point split endpoint 4096 180)/2)
    have hp : upperPayment 179 = (414288789653:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 179+point split endpoint 4096 180)/2 = (580665977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580665977:ℝ)/168755200)*ClassicalSixthBranch.v ((580665977:ℝ)/168755200)/ClassicalSixthBranch.r = (158330336102081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_179
  · change upperPayment 180 ≤ upperValue ((point split endpoint 4096 180+point split endpoint 4096 181)/2)
    have hp : upperPayment 180 = (414231225437:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 180+point split endpoint 4096 181)/2 = (580691127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580691127:ℝ)/168755200)*ClassicalSixthBranch.v ((580691127:ℝ)/168755200)/ClassicalSixthBranch.r = (158304683118177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_180
  · change upperPayment 181 ≤ upperValue ((point split endpoint 4096 181+point split endpoint 4096 182)/2)
    have hp : upperPayment 181 = (414173641577:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 181+point split endpoint 4096 182)/2 = (580716277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580716277:ℝ)/168755200)*ClassicalSixthBranch.v ((580716277:ℝ)/168755200)/ClassicalSixthBranch.r = (158279032158345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_181
  · change upperPayment 182 ≤ upperValue ((point split endpoint 4096 182+point split endpoint 4096 183)/2)
    have hp : upperPayment 182 = (414116038069:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 182+point split endpoint 4096 183)/2 = (580741427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580741427:ℝ)/168755200)*ClassicalSixthBranch.v ((580741427:ℝ)/168755200)/ClassicalSixthBranch.r = (158253383222585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_182
  · change upperPayment 183 ≤ upperValue ((point split endpoint 4096 183+point split endpoint 4096 184)/2)
    have hp : upperPayment 183 = (414058414913:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 183+point split endpoint 4096 184)/2 = (580766577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580766577:ℝ)/168755200)*ClassicalSixthBranch.v ((580766577:ℝ)/168755200)/ClassicalSixthBranch.r = (158227736310897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_183
  · change upperPayment 184 ≤ upperValue ((point split endpoint 4096 184+point split endpoint 4096 185)/2)
    have hp : upperPayment 184 = (414000772104:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 184+point split endpoint 4096 185)/2 = (580791727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580791727:ℝ)/168755200)*ClassicalSixthBranch.v ((580791727:ℝ)/168755200)/ClassicalSixthBranch.r = (158202091423281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_184
  · change upperPayment 185 ≤ upperValue ((point split endpoint 4096 185+point split endpoint 4096 186)/2)
    have hp : upperPayment 185 = (413943109642:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 185+point split endpoint 4096 186)/2 = (580816877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580816877:ℝ)/168755200)*ClassicalSixthBranch.v ((580816877:ℝ)/168755200)/ClassicalSixthBranch.r = (158176448559737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_185
  · change upperPayment 186 ≤ upperValue ((point split endpoint 4096 186+point split endpoint 4096 187)/2)
    have hp : upperPayment 186 = (413885427524:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 186+point split endpoint 4096 187)/2 = (580842027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580842027:ℝ)/168755200)*ClassicalSixthBranch.v ((580842027:ℝ)/168755200)/ClassicalSixthBranch.r = (158150807720265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_186
  · change upperPayment 187 ≤ upperValue ((point split endpoint 4096 187+point split endpoint 4096 188)/2)
    have hp : upperPayment 187 = (413827725747:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 187+point split endpoint 4096 188)/2 = (580867177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580867177:ℝ)/168755200)*ClassicalSixthBranch.v ((580867177:ℝ)/168755200)/ClassicalSixthBranch.r = (158125168904865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_187
  · change upperPayment 188 ≤ upperValue ((point split endpoint 4096 188+point split endpoint 4096 189)/2)
    have hp : upperPayment 188 = (413770004309:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 188+point split endpoint 4096 189)/2 = (580892327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580892327:ℝ)/168755200)*ClassicalSixthBranch.v ((580892327:ℝ)/168755200)/ClassicalSixthBranch.r = (158099532113537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_188
  · change upperPayment 189 ≤ upperValue ((point split endpoint 4096 189+point split endpoint 4096 190)/2)
    have hp : upperPayment 189 = (413712263209:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 189+point split endpoint 4096 190)/2 = (580917477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580917477:ℝ)/168755200)*ClassicalSixthBranch.v ((580917477:ℝ)/168755200)/ClassicalSixthBranch.r = (158073897346281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_189
  · change upperPayment 190 ≤ upperValue ((point split endpoint 4096 190+point split endpoint 4096 191)/2)
    have hp : upperPayment 190 = (413654502442:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 190+point split endpoint 4096 191)/2 = (580942627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580942627:ℝ)/168755200)*ClassicalSixthBranch.v ((580942627:ℝ)/168755200)/ClassicalSixthBranch.r = (158048264603097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_190
  · change upperPayment 191 ≤ upperValue ((point split endpoint 4096 191+point split endpoint 4096 192)/2)
    have hp : upperPayment 191 = (413596722008:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 191+point split endpoint 4096 192)/2 = (580967777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580967777:ℝ)/168755200)*ClassicalSixthBranch.v ((580967777:ℝ)/168755200)/ClassicalSixthBranch.r = (158022633883985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_191
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_011
