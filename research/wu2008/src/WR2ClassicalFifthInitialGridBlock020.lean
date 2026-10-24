import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints020
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_020 (j : Fin 16) : initialPayment (16*20+j.val) ≤
    initialValue ((point lo 4 1024 (16*20+j.val)+point lo 4 1024 (16*20+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 320 ≤ initialValue ((point lo 4 1024 320+point lo 4 1024 321)/2)
    have hp : initialPayment 320 = (140128284002:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 320+point lo 4 1024 321)/2 = (151774117:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151774117:ℝ)/42188800) = (67942400:ℝ)/60206171 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_320
  · change initialPayment 321 ≤ initialValue ((point lo 4 1024 321+point lo 4 1024 322)/2)
    have hp : initialPayment 321 = (140629685914:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 321+point lo 4 1024 322)/2 = (30359651:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30359651:ℝ)/8437760) = (67942400:ℝ)/60182033 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_321
  · change initialPayment 322 ≤ initialValue ((point lo 4 1024 322+point lo 4 1024 323)/2)
    have hp : initialPayment 322 = (141131519637:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 322+point lo 4 1024 323)/2 = (151822393:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151822393:ℝ)/42188800) = (13588480:ℝ)/12031579 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_322
  · change initialPayment 323 ≤ initialValue ((point lo 4 1024 323+point lo 4 1024 324)/2)
    have hp : initialPayment 323 = (141633785510:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 323+point lo 4 1024 324)/2 = (151846531:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151846531:ℝ)/42188800) = (67942400:ℝ)/60133757 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_323
  · change initialPayment 324 ≤ initialValue ((point lo 4 1024 324+point lo 4 1024 325)/2)
    have hp : initialPayment 324 = (142136483873:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 324+point lo 4 1024 325)/2 = (151870669:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151870669:ℝ)/42188800) = (67942400:ℝ)/60109619 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_324
  · change initialPayment 325 ≤ initialValue ((point lo 4 1024 325+point lo 4 1024 326)/2)
    have hp : initialPayment 325 = (142639615067:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 325+point lo 4 1024 326)/2 = (151894807:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151894807:ℝ)/42188800) = (67942400:ℝ)/60085481 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_325
  · change initialPayment 326 ≤ initialValue ((point lo 4 1024 326+point lo 4 1024 327)/2)
    have hp : initialPayment 326 = (143143179432:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 326+point lo 4 1024 327)/2 = (30383789:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30383789:ℝ)/8437760) = (67942400:ℝ)/60061343 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_326
  · change initialPayment 327 ≤ initialValue ((point lo 4 1024 327+point lo 4 1024 328)/2)
    have hp : initialPayment 327 = (143647177310:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 327+point lo 4 1024 328)/2 = (151943083:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151943083:ℝ)/42188800) = (13588480:ℝ)/12007441 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_327
  · change initialPayment 328 ≤ initialValue ((point lo 4 1024 328+point lo 4 1024 329)/2)
    have hp : initialPayment 328 = (144151609043:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 328+point lo 4 1024 329)/2 = (151967221:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151967221:ℝ)/42188800) = (67942400:ℝ)/60013067 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_328
  · change initialPayment 329 ≤ initialValue ((point lo 4 1024 329+point lo 4 1024 330)/2)
    have hp : initialPayment 329 = (144656474973:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 329+point lo 4 1024 330)/2 = (151991359:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((151991359:ℝ)/42188800) = (67942400:ℝ)/59988929 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_329
  · change initialPayment 330 ≤ initialValue ((point lo 4 1024 330+point lo 4 1024 331)/2)
    have hp : initialPayment 330 = (145161775444:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 330+point lo 4 1024 331)/2 = (152015497:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152015497:ℝ)/42188800) = (67942400:ℝ)/59964791 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_330
  · change initialPayment 331 ≤ initialValue ((point lo 4 1024 331+point lo 4 1024 332)/2)
    have hp : initialPayment 331 = (145667510798:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 331+point lo 4 1024 332)/2 = (30407927:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30407927:ℝ)/8437760) = (67942400:ℝ)/59940653 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_331
  · change initialPayment 332 ≤ initialValue ((point lo 4 1024 332+point lo 4 1024 333)/2)
    have hp : initialPayment 332 = (146173681380:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 332+point lo 4 1024 333)/2 = (152063773:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152063773:ℝ)/42188800) = (13588480:ℝ)/11983303 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_332
  · change initialPayment 333 ≤ initialValue ((point lo 4 1024 333+point lo 4 1024 334)/2)
    have hp : initialPayment 333 = (146680287534:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 333+point lo 4 1024 334)/2 = (152087911:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152087911:ℝ)/42188800) = (67942400:ℝ)/59892377 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_333
  · change initialPayment 334 ≤ initialValue ((point lo 4 1024 334+point lo 4 1024 335)/2)
    have hp : initialPayment 334 = (147187329605:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 334+point lo 4 1024 335)/2 = (152112049:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152112049:ℝ)/42188800) = (67942400:ℝ)/59868239 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_334
  · change initialPayment 335 ≤ initialValue ((point lo 4 1024 335+point lo 4 1024 336)/2)
    have hp : initialPayment 335 = (147694807938:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 335+point lo 4 1024 336)/2 = (152136187:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152136187:ℝ)/42188800) = (67942400:ℝ)/59844101 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_335
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_020
