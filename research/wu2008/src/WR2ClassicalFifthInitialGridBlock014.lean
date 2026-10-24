import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints014
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_014 (j : Fin 16) : initialPayment (16*14+j.val) ≤
    initialValue ((point lo 4 1024 (16*14+j.val)+point lo 4 1024 (16*14+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 224 ≤ initialValue ((point lo 4 1024 224+point lo 4 1024 225)/2)
    have hp : initialPayment 224 = (93954401344:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 224+point lo 4 1024 225)/2 = (149456869:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149456869:ℝ)/42188800) = (67942400:ℝ)/62523419 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_224
  · change initialPayment 225 ≤ initialValue ((point lo 4 1024 225+point lo 4 1024 226)/2)
    have hp : initialPayment 225 = (94415856897:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 225+point lo 4 1024 226)/2 = (149481007:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149481007:ℝ)/42188800) = (67942400:ℝ)/62499281 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_225
  · change initialPayment 226 ≤ initialValue ((point lo 4 1024 226+point lo 4 1024 227)/2)
    have hp : initialPayment 226 = (94877713885:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 226+point lo 4 1024 227)/2 = (29901029:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29901029:ℝ)/8437760) = (67942400:ℝ)/62475143 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_226
  · change initialPayment 227 ≤ initialValue ((point lo 4 1024 227+point lo 4 1024 228)/2)
    have hp : initialPayment 227 = (95339972601:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 227+point lo 4 1024 228)/2 = (149529283:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149529283:ℝ)/42188800) = (13588480:ℝ)/12490201 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_227
  · change initialPayment 228 ≤ initialValue ((point lo 4 1024 228+point lo 4 1024 229)/2)
    have hp : initialPayment 228 = (95802633342:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 228+point lo 4 1024 229)/2 = (149553421:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149553421:ℝ)/42188800) = (67942400:ℝ)/62426867 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_228
  · change initialPayment 229 ≤ initialValue ((point lo 4 1024 229+point lo 4 1024 230)/2)
    have hp : initialPayment 229 = (96265696402:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 229+point lo 4 1024 230)/2 = (149577559:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149577559:ℝ)/42188800) = (67942400:ℝ)/62402729 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_229
  · change initialPayment 230 ≤ initialValue ((point lo 4 1024 230+point lo 4 1024 231)/2)
    have hp : initialPayment 230 = (96729162079:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 230+point lo 4 1024 231)/2 = (149601697:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149601697:ℝ)/42188800) = (67942400:ℝ)/62378591 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_230
  · change initialPayment 231 ≤ initialValue ((point lo 4 1024 231+point lo 4 1024 232)/2)
    have hp : initialPayment 231 = (97193030668:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 231+point lo 4 1024 232)/2 = (29925167:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29925167:ℝ)/8437760) = (67942400:ℝ)/62354453 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_231
  · change initialPayment 232 ≤ initialValue ((point lo 4 1024 232+point lo 4 1024 233)/2)
    have hp : initialPayment 232 = (97657302466:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 232+point lo 4 1024 233)/2 = (149649973:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149649973:ℝ)/42188800) = (13588480:ℝ)/12466063 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_232
  · change initialPayment 233 ≤ initialValue ((point lo 4 1024 233+point lo 4 1024 234)/2)
    have hp : initialPayment 233 = (98121977772:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 233+point lo 4 1024 234)/2 = (149674111:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149674111:ℝ)/42188800) = (67942400:ℝ)/62306177 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_233
  · change initialPayment 234 ≤ initialValue ((point lo 4 1024 234+point lo 4 1024 235)/2)
    have hp : initialPayment 234 = (98587056883:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 234+point lo 4 1024 235)/2 = (149698249:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149698249:ℝ)/42188800) = (67942400:ℝ)/62282039 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_234
  · change initialPayment 235 ≤ initialValue ((point lo 4 1024 235+point lo 4 1024 236)/2)
    have hp : initialPayment 235 = (99052540097:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 235+point lo 4 1024 236)/2 = (149722387:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149722387:ℝ)/42188800) = (67942400:ℝ)/62257901 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_235
  · change initialPayment 236 ≤ initialValue ((point lo 4 1024 236+point lo 4 1024 237)/2)
    have hp : initialPayment 236 = (99518427713:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 236+point lo 4 1024 237)/2 = (5989861:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((5989861:ℝ)/1687552) = (67942400:ℝ)/62233763 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_236
  · change initialPayment 237 ≤ initialValue ((point lo 4 1024 237+point lo 4 1024 238)/2)
    have hp : initialPayment 237 = (99984720031:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 237+point lo 4 1024 238)/2 = (149770663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149770663:ℝ)/42188800) = (2717696:ℝ)/2488385 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_237
  · change initialPayment 238 ≤ initialValue ((point lo 4 1024 238+point lo 4 1024 239)/2)
    have hp : initialPayment 238 = (100451417350:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 238+point lo 4 1024 239)/2 = (149794801:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149794801:ℝ)/42188800) = (67942400:ℝ)/62185487 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_238
  · change initialPayment 239 ≤ initialValue ((point lo 4 1024 239+point lo 4 1024 240)/2)
    have hp : initialPayment 239 = (100918519970:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 239+point lo 4 1024 240)/2 = (149818939:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((149818939:ℝ)/42188800) = (67942400:ℝ)/62161349 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_239
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_014
