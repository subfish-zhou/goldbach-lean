import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints011
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_011 (j : Fin 16) : initialPayment (16*11+j.val) ≤
    initialValue ((point lo 4 1024 (16*11+j.val)+point lo 4 1024 (16*11+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 176 ≤ initialValue ((point lo 4 1024 176+point lo 4 1024 177)/2)
    have hp : initialPayment 176 = (72270949206:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 176+point lo 4 1024 177)/2 = (29659649:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29659649:ℝ)/8437760) = (67942400:ℝ)/63682043 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_176
  · change initialPayment 177 ≤ initialValue ((point lo 4 1024 177+point lo 4 1024 178)/2)
    have hp : initialPayment 177 = (72713474293:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 177+point lo 4 1024 178)/2 = (148322383:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148322383:ℝ)/42188800) = (13588480:ℝ)/12731581 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_177
  · change initialPayment 178 ≤ initialValue ((point lo 4 1024 178+point lo 4 1024 179)/2)
    have hp : initialPayment 178 = (73156387162:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 178+point lo 4 1024 179)/2 = (148346521:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148346521:ℝ)/42188800) = (67942400:ℝ)/63633767 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_178
  · change initialPayment 179 ≤ initialValue ((point lo 4 1024 179+point lo 4 1024 180)/2)
    have hp : initialPayment 179 = (73599688087:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 179+point lo 4 1024 180)/2 = (148370659:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148370659:ℝ)/42188800) = (67942400:ℝ)/63609629 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_179
  · change initialPayment 180 ≤ initialValue ((point lo 4 1024 180+point lo 4 1024 181)/2)
    have hp : initialPayment 180 = (74043377343:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 180+point lo 4 1024 181)/2 = (148394797:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148394797:ℝ)/42188800) = (67942400:ℝ)/63585491 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_180
  · change initialPayment 181 ≤ initialValue ((point lo 4 1024 181+point lo 4 1024 182)/2)
    have hp : initialPayment 181 = (74487455206:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 181+point lo 4 1024 182)/2 = (29683787:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29683787:ℝ)/8437760) = (67942400:ℝ)/63561353 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_181
  · change initialPayment 182 ≤ initialValue ((point lo 4 1024 182+point lo 4 1024 183)/2)
    have hp : initialPayment 182 = (74931921951:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 182+point lo 4 1024 183)/2 = (148443073:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148443073:ℝ)/42188800) = (13588480:ℝ)/12707443 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_182
  · change initialPayment 183 ≤ initialValue ((point lo 4 1024 183+point lo 4 1024 184)/2)
    have hp : initialPayment 183 = (75376777855:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 183+point lo 4 1024 184)/2 = (148467211:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148467211:ℝ)/42188800) = (67942400:ℝ)/63513077 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_183
  · change initialPayment 184 ≤ initialValue ((point lo 4 1024 184+point lo 4 1024 185)/2)
    have hp : initialPayment 184 = (75822023194:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 184+point lo 4 1024 185)/2 = (148491349:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148491349:ℝ)/42188800) = (67942400:ℝ)/63488939 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_184
  · change initialPayment 185 ≤ initialValue ((point lo 4 1024 185+point lo 4 1024 186)/2)
    have hp : initialPayment 185 = (76267658246:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 185+point lo 4 1024 186)/2 = (148515487:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148515487:ℝ)/42188800) = (67942400:ℝ)/63464801 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_185
  · change initialPayment 186 ≤ initialValue ((point lo 4 1024 186+point lo 4 1024 187)/2)
    have hp : initialPayment 186 = (76713683287:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 186+point lo 4 1024 187)/2 = (5941585:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((5941585:ℝ)/1687552) = (67942400:ℝ)/63440663 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_186
  · change initialPayment 187 ≤ initialValue ((point lo 4 1024 187+point lo 4 1024 188)/2)
    have hp : initialPayment 187 = (77160098597:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 187+point lo 4 1024 188)/2 = (148563763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148563763:ℝ)/42188800) = (2717696:ℝ)/2536661 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_187
  · change initialPayment 188 ≤ initialValue ((point lo 4 1024 188+point lo 4 1024 189)/2)
    have hp : initialPayment 188 = (77606904453:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 188+point lo 4 1024 189)/2 = (148587901:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148587901:ℝ)/42188800) = (67942400:ℝ)/63392387 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_188
  · change initialPayment 189 ≤ initialValue ((point lo 4 1024 189+point lo 4 1024 190)/2)
    have hp : initialPayment 189 = (78054101134:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 189+point lo 4 1024 190)/2 = (148612039:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148612039:ℝ)/42188800) = (67942400:ℝ)/63368249 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_189
  · change initialPayment 190 ≤ initialValue ((point lo 4 1024 190+point lo 4 1024 191)/2)
    have hp : initialPayment 190 = (78501688919:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 190+point lo 4 1024 191)/2 = (148636177:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148636177:ℝ)/42188800) = (67942400:ℝ)/63344111 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_190
  · change initialPayment 191 ≤ initialValue ((point lo 4 1024 191+point lo 4 1024 192)/2)
    have hp : initialPayment 191 = (78949668087:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 191+point lo 4 1024 192)/2 = (29732063:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29732063:ℝ)/8437760) = (67942400:ℝ)/63319973 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_191
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_011
