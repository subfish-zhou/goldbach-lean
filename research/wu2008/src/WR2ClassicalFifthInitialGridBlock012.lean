import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints012
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_012 (j : Fin 16) : initialPayment (16*12+j.val) ≤
    initialValue ((point lo 4 1024 (16*12+j.val)+point lo 4 1024 (16*12+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 192 ≤ initialValue ((point lo 4 1024 192+point lo 4 1024 193)/2)
    have hp : initialPayment 192 = (79398038920:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 192+point lo 4 1024 193)/2 = (148684453:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148684453:ℝ)/42188800) = (13588480:ℝ)/12659167 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_192
  · change initialPayment 193 ≤ initialValue ((point lo 4 1024 193+point lo 4 1024 194)/2)
    have hp : initialPayment 193 = (79846801696:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 193+point lo 4 1024 194)/2 = (148708591:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148708591:ℝ)/42188800) = (67942400:ℝ)/63271697 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_193
  · change initialPayment 194 ≤ initialValue ((point lo 4 1024 194+point lo 4 1024 195)/2)
    have hp : initialPayment 194 = (80295956697:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 194+point lo 4 1024 195)/2 = (148732729:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148732729:ℝ)/42188800) = (67942400:ℝ)/63247559 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_194
  · change initialPayment 195 ≤ initialValue ((point lo 4 1024 195+point lo 4 1024 196)/2)
    have hp : initialPayment 195 = (80745504205:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 195+point lo 4 1024 196)/2 = (148756867:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148756867:ℝ)/42188800) = (67942400:ℝ)/63223421 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_195
  · change initialPayment 196 ≤ initialValue ((point lo 4 1024 196+point lo 4 1024 197)/2)
    have hp : initialPayment 196 = (81195444500:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 196+point lo 4 1024 197)/2 = (29756201:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29756201:ℝ)/8437760) = (67942400:ℝ)/63199283 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_196
  · change initialPayment 197 ≤ initialValue ((point lo 4 1024 197+point lo 4 1024 198)/2)
    have hp : initialPayment 197 = (81645777865:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 197+point lo 4 1024 198)/2 = (148805143:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148805143:ℝ)/42188800) = (13588480:ℝ)/12635029 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_197
  · change initialPayment 198 ≤ initialValue ((point lo 4 1024 198+point lo 4 1024 199)/2)
    have hp : initialPayment 198 = (82096504583:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 198+point lo 4 1024 199)/2 = (148829281:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148829281:ℝ)/42188800) = (67942400:ℝ)/63151007 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_198
  · change initialPayment 199 ≤ initialValue ((point lo 4 1024 199+point lo 4 1024 200)/2)
    have hp : initialPayment 199 = (82547624935:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 199+point lo 4 1024 200)/2 = (148853419:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148853419:ℝ)/42188800) = (67942400:ℝ)/63126869 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_199
  · change initialPayment 200 ≤ initialValue ((point lo 4 1024 200+point lo 4 1024 201)/2)
    have hp : initialPayment 200 = (82999139207:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 200+point lo 4 1024 201)/2 = (148877557:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148877557:ℝ)/42188800) = (67942400:ℝ)/63102731 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_200
  · change initialPayment 201 ≤ initialValue ((point lo 4 1024 201+point lo 4 1024 202)/2)
    have hp : initialPayment 201 = (83451047680:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 201+point lo 4 1024 202)/2 = (29780339:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29780339:ℝ)/8437760) = (67942400:ℝ)/63078593 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_201
  · change initialPayment 202 ≤ initialValue ((point lo 4 1024 202+point lo 4 1024 203)/2)
    have hp : initialPayment 202 = (83903350640:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 202+point lo 4 1024 203)/2 = (148925833:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148925833:ℝ)/42188800) = (13588480:ℝ)/12610891 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_202
  · change initialPayment 203 ≤ initialValue ((point lo 4 1024 203+point lo 4 1024 204)/2)
    have hp : initialPayment 203 = (84356048371:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 203+point lo 4 1024 204)/2 = (148949971:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148949971:ℝ)/42188800) = (67942400:ℝ)/63030317 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_203
  · change initialPayment 204 ≤ initialValue ((point lo 4 1024 204+point lo 4 1024 205)/2)
    have hp : initialPayment 204 = (84809141159:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 204+point lo 4 1024 205)/2 = (148974109:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148974109:ℝ)/42188800) = (67942400:ℝ)/63006179 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_204
  · change initialPayment 205 ≤ initialValue ((point lo 4 1024 205+point lo 4 1024 206)/2)
    have hp : initialPayment 205 = (85262629287:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 205+point lo 4 1024 206)/2 = (148998247:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((148998247:ℝ)/42188800) = (67942400:ℝ)/62982041 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_205
  · change initialPayment 206 ≤ initialValue ((point lo 4 1024 206+point lo 4 1024 207)/2)
    have hp : initialPayment 206 = (85716513043:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 206+point lo 4 1024 207)/2 = (29804477:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29804477:ℝ)/8437760) = (67942400:ℝ)/62957903 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_206
  · change initialPayment 207 ≤ initialValue ((point lo 4 1024 207+point lo 4 1024 208)/2)
    have hp : initialPayment 207 = (86170792713:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 207+point lo 4 1024 208)/2 = (149046523:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149046523:ℝ)/42188800) = (13588480:ℝ)/12586753 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_207
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_012
