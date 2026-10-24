import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints019
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_019 (j : Fin 16) : initialPayment (16*19+j.val) ≤
    initialValue ((point lo 4 1024 (16*19+j.val)+point lo 4 1024 (16*19+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 304 ≤ initialValue ((point lo 4 1024 304+point lo 4 1024 305)/2)
    have hp : initialPayment 304 = (132164304604:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 304+point lo 4 1024 305)/2 = (151387909:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151387909:ℝ)/42188800) = (67942400:ℝ)/60592379 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_304
  · change initialPayment 305 ≤ initialValue ((point lo 4 1024 305+point lo 4 1024 306)/2)
    have hp : initialPayment 305 = (132658843306:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 305+point lo 4 1024 306)/2 = (151412047:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151412047:ℝ)/42188800) = (67942400:ℝ)/60568241 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_305
  · change initialPayment 306 ≤ initialValue ((point lo 4 1024 306+point lo 4 1024 307)/2)
    have hp : initialPayment 306 = (133153808454:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 306+point lo 4 1024 307)/2 = (30287237:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30287237:ℝ)/8437760) = (67942400:ℝ)/60544103 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_306
  · change initialPayment 307 ≤ initialValue ((point lo 4 1024 307+point lo 4 1024 308)/2)
    have hp : initialPayment 307 = (133649200380:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 307+point lo 4 1024 308)/2 = (151460323:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151460323:ℝ)/42188800) = (13588480:ℝ)/12103993 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_307
  · change initialPayment 308 ≤ initialValue ((point lo 4 1024 308+point lo 4 1024 309)/2)
    have hp : initialPayment 308 = (134145019416:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 308+point lo 4 1024 309)/2 = (151484461:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151484461:ℝ)/42188800) = (67942400:ℝ)/60495827 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_308
  · change initialPayment 309 ≤ initialValue ((point lo 4 1024 309+point lo 4 1024 310)/2)
    have hp : initialPayment 309 = (134641265896:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 309+point lo 4 1024 310)/2 = (151508599:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151508599:ℝ)/42188800) = (67942400:ℝ)/60471689 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_309
  · change initialPayment 310 ≤ initialValue ((point lo 4 1024 310+point lo 4 1024 311)/2)
    have hp : initialPayment 310 = (135137940151:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 310+point lo 4 1024 311)/2 = (151532737:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151532737:ℝ)/42188800) = (67942400:ℝ)/60447551 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_310
  · change initialPayment 311 ≤ initialValue ((point lo 4 1024 311+point lo 4 1024 312)/2)
    have hp : initialPayment 311 = (135635042516:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 311+point lo 4 1024 312)/2 = (6062275:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6062275:ℝ)/1687552) = (67942400:ℝ)/60423413 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_311
  · change initialPayment 312 ≤ initialValue ((point lo 4 1024 312+point lo 4 1024 313)/2)
    have hp : initialPayment 312 = (136132573325:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 312+point lo 4 1024 313)/2 = (151581013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151581013:ℝ)/42188800) = (2717696:ℝ)/2415971 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_312
  · change initialPayment 313 ≤ initialValue ((point lo 4 1024 313+point lo 4 1024 314)/2)
    have hp : initialPayment 313 = (136630532911:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 313+point lo 4 1024 314)/2 = (151605151:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151605151:ℝ)/42188800) = (67942400:ℝ)/60375137 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_313
  · change initialPayment 314 ≤ initialValue ((point lo 4 1024 314+point lo 4 1024 315)/2)
    have hp : initialPayment 314 = (137128921610:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 314+point lo 4 1024 315)/2 = (151629289:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151629289:ℝ)/42188800) = (67942400:ℝ)/60350999 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_314
  · change initialPayment 315 ≤ initialValue ((point lo 4 1024 315+point lo 4 1024 316)/2)
    have hp : initialPayment 315 = (137627739758:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 315+point lo 4 1024 316)/2 = (151653427:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151653427:ℝ)/42188800) = (67942400:ℝ)/60326861 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_315
  · change initialPayment 316 ≤ initialValue ((point lo 4 1024 316+point lo 4 1024 317)/2)
    have hp : initialPayment 316 = (138126987691:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 316+point lo 4 1024 317)/2 = (30335513:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30335513:ℝ)/8437760) = (67942400:ℝ)/60302723 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_316
  · change initialPayment 317 ≤ initialValue ((point lo 4 1024 317+point lo 4 1024 318)/2)
    have hp : initialPayment 317 = (138626665744:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 317+point lo 4 1024 318)/2 = (151701703:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151701703:ℝ)/42188800) = (13588480:ℝ)/12055717 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_317
  · change initialPayment 318 ≤ initialValue ((point lo 4 1024 318+point lo 4 1024 319)/2)
    have hp : initialPayment 318 = (139126774255:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 318+point lo 4 1024 319)/2 = (151725841:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151725841:ℝ)/42188800) = (67942400:ℝ)/60254447 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_318
  · change initialPayment 319 ≤ initialValue ((point lo 4 1024 319+point lo 4 1024 320)/2)
    have hp : initialPayment 319 = (139627313562:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 319+point lo 4 1024 320)/2 = (151749979:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151749979:ℝ)/42188800) = (67942400:ℝ)/60230309 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_319
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_019
