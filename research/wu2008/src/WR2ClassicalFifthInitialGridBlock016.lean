import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints016
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_016 (j : Fin 16) : initialPayment (16*16+j.val) ≤
    initialValue ((point lo 4 1024 (16*16+j.val)+point lo 4 1024 (16*16+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 256 ≤ initialValue ((point lo 4 1024 256+point lo 4 1024 257)/2)
    have hp : initialPayment 256 = (108921568552:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 256+point lo 4 1024 257)/2 = (30045857:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30045857:ℝ)/8437760) = (67942400:ℝ)/61751003 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_256
  · change initialPayment 257 ≤ initialValue ((point lo 4 1024 257+point lo 4 1024 258)/2)
    have hp : initialPayment 257 = (109396018420:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 257+point lo 4 1024 258)/2 = (150253423:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150253423:ℝ)/42188800) = (13588480:ℝ)/12345373 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_257
  · change initialPayment 258 ≤ initialValue ((point lo 4 1024 258+point lo 4 1024 259)/2)
    have hp : initialPayment 258 = (109870879376:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 258+point lo 4 1024 259)/2 = (150277561:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150277561:ℝ)/42188800) = (67942400:ℝ)/61702727 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_258
  · change initialPayment 259 ≤ initialValue ((point lo 4 1024 259+point lo 4 1024 260)/2)
    have hp : initialPayment 259 = (110346151728:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 259+point lo 4 1024 260)/2 = (150301699:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150301699:ℝ)/42188800) = (67942400:ℝ)/61678589 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_259
  · change initialPayment 260 ≤ initialValue ((point lo 4 1024 260+point lo 4 1024 261)/2)
    have hp : initialPayment 260 = (110821835788:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 260+point lo 4 1024 261)/2 = (150325837:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150325837:ℝ)/42188800) = (67942400:ℝ)/61654451 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_260
  · change initialPayment 261 ≤ initialValue ((point lo 4 1024 261+point lo 4 1024 262)/2)
    have hp : initialPayment 261 = (111297931864:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 261+point lo 4 1024 262)/2 = (6013999:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6013999:ℝ)/1687552) = (67942400:ℝ)/61630313 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_261
  · change initialPayment 262 ≤ initialValue ((point lo 4 1024 262+point lo 4 1024 263)/2)
    have hp : initialPayment 262 = (111774440267:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 262+point lo 4 1024 263)/2 = (150374113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150374113:ℝ)/42188800) = (2717696:ℝ)/2464247 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_262
  · change initialPayment 263 ≤ initialValue ((point lo 4 1024 263+point lo 4 1024 264)/2)
    have hp : initialPayment 263 = (112251361308:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 263+point lo 4 1024 264)/2 = (150398251:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150398251:ℝ)/42188800) = (67942400:ℝ)/61582037 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_263
  · change initialPayment 264 ≤ initialValue ((point lo 4 1024 264+point lo 4 1024 265)/2)
    have hp : initialPayment 264 = (112728695298:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 264+point lo 4 1024 265)/2 = (150422389:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150422389:ℝ)/42188800) = (67942400:ℝ)/61557899 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_264
  · change initialPayment 265 ≤ initialValue ((point lo 4 1024 265+point lo 4 1024 266)/2)
    have hp : initialPayment 265 = (113206442549:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 265+point lo 4 1024 266)/2 = (150446527:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150446527:ℝ)/42188800) = (67942400:ℝ)/61533761 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_265
  · change initialPayment 266 ≤ initialValue ((point lo 4 1024 266+point lo 4 1024 267)/2)
    have hp : initialPayment 266 = (113684603374:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 266+point lo 4 1024 267)/2 = (30094133:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30094133:ℝ)/8437760) = (67942400:ℝ)/61509623 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_266
  · change initialPayment 267 ≤ initialValue ((point lo 4 1024 267+point lo 4 1024 268)/2)
    have hp : initialPayment 267 = (114163178084:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 267+point lo 4 1024 268)/2 = (150494803:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150494803:ℝ)/42188800) = (13588480:ℝ)/12297097 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_267
  · change initialPayment 268 ≤ initialValue ((point lo 4 1024 268+point lo 4 1024 269)/2)
    have hp : initialPayment 268 = (114642166994:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 268+point lo 4 1024 269)/2 = (150518941:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150518941:ℝ)/42188800) = (67942400:ℝ)/61461347 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_268
  · change initialPayment 269 ≤ initialValue ((point lo 4 1024 269+point lo 4 1024 270)/2)
    have hp : initialPayment 269 = (115121570417:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 269+point lo 4 1024 270)/2 = (150543079:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150543079:ℝ)/42188800) = (67942400:ℝ)/61437209 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_269
  · change initialPayment 270 ≤ initialValue ((point lo 4 1024 270+point lo 4 1024 271)/2)
    have hp : initialPayment 270 = (115601388666:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 270+point lo 4 1024 271)/2 = (150567217:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((150567217:ℝ)/42188800) = (67942400:ℝ)/61413071 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_270
  · change initialPayment 271 ≤ initialValue ((point lo 4 1024 271+point lo 4 1024 272)/2)
    have hp : initialPayment 271 = (116081622058:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 271+point lo 4 1024 272)/2 = (30118271:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30118271:ℝ)/8437760) = (67942400:ℝ)/61388933 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_271
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_016
