import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints023
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_023 (j : Fin 16) : initialPayment (16*23+j.val) ≤
    initialValue ((point lo 4 1024 (16*23+j.val)+point lo 4 1024 (16*23+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 368 ≤ initialValue ((point lo 4 1024 368+point lo 4 1024 369)/2)
    have hp : initialPayment 368 = (164688627169:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 368+point lo 4 1024 369)/2 = (152932741:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152932741:ℝ)/42188800) = (67942400:ℝ)/59047547 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_368
  · change initialPayment 369 ≤ initialValue ((point lo 4 1024 369+point lo 4 1024 370)/2)
    have hp : initialPayment 369 = (165211147618:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 369+point lo 4 1024 370)/2 = (152956879:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152956879:ℝ)/42188800) = (67942400:ℝ)/59023409 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_369
  · change initialPayment 370 ≤ initialValue ((point lo 4 1024 370+point lo 4 1024 371)/2)
    have hp : initialPayment 370 = (165734116743:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 370+point lo 4 1024 371)/2 = (152981017:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152981017:ℝ)/42188800) = (67942400:ℝ)/58999271 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_370
  · change initialPayment 371 ≤ initialValue ((point lo 4 1024 371+point lo 4 1024 372)/2)
    have hp : initialPayment 371 = (166257534909:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 371+point lo 4 1024 372)/2 = (30601031:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30601031:ℝ)/8437760) = (67942400:ℝ)/58975133 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_371
  · change initialPayment 372 ≤ initialValue ((point lo 4 1024 372+point lo 4 1024 373)/2)
    have hp : initialPayment 372 = (166781402481:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 372+point lo 4 1024 373)/2 = (153029293:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153029293:ℝ)/42188800) = (13588480:ℝ)/11790199 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_372
  · change initialPayment 373 ≤ initialValue ((point lo 4 1024 373+point lo 4 1024 374)/2)
    have hp : initialPayment 373 = (167305719823:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 373+point lo 4 1024 374)/2 = (153053431:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153053431:ℝ)/42188800) = (67942400:ℝ)/58926857 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_373
  · change initialPayment 374 ≤ initialValue ((point lo 4 1024 374+point lo 4 1024 375)/2)
    have hp : initialPayment 374 = (167830487301:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 374+point lo 4 1024 375)/2 = (153077569:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153077569:ℝ)/42188800) = (67942400:ℝ)/58902719 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_374
  · change initialPayment 375 ≤ initialValue ((point lo 4 1024 375+point lo 4 1024 376)/2)
    have hp : initialPayment 375 = (168355705282:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 375+point lo 4 1024 376)/2 = (153101707:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153101707:ℝ)/42188800) = (67942400:ℝ)/58878581 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_375
  · change initialPayment 376 ≤ initialValue ((point lo 4 1024 376+point lo 4 1024 377)/2)
    have hp : initialPayment 376 = (168881374133:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 376+point lo 4 1024 377)/2 = (30625169:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30625169:ℝ)/8437760) = (67942400:ℝ)/58854443 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_376
  · change initialPayment 377 ≤ initialValue ((point lo 4 1024 377+point lo 4 1024 378)/2)
    have hp : initialPayment 377 = (169407494219:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 377+point lo 4 1024 378)/2 = (153149983:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153149983:ℝ)/42188800) = (13588480:ℝ)/11766061 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_377
  · change initialPayment 378 ≤ initialValue ((point lo 4 1024 378+point lo 4 1024 379)/2)
    have hp : initialPayment 378 = (169934065911:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 378+point lo 4 1024 379)/2 = (153174121:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153174121:ℝ)/42188800) = (67942400:ℝ)/58806167 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_378
  · change initialPayment 379 ≤ initialValue ((point lo 4 1024 379+point lo 4 1024 380)/2)
    have hp : initialPayment 379 = (170461089575:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 379+point lo 4 1024 380)/2 = (153198259:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153198259:ℝ)/42188800) = (67942400:ℝ)/58782029 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_379
  · change initialPayment 380 ≤ initialValue ((point lo 4 1024 380+point lo 4 1024 381)/2)
    have hp : initialPayment 380 = (170988565581:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 380+point lo 4 1024 381)/2 = (153222397:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153222397:ℝ)/42188800) = (67942400:ℝ)/58757891 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_380
  · change initialPayment 381 ≤ initialValue ((point lo 4 1024 381+point lo 4 1024 382)/2)
    have hp : initialPayment 381 = (171516494298:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 381+point lo 4 1024 382)/2 = (30649307:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30649307:ℝ)/8437760) = (67942400:ℝ)/58733753 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_381
  · change initialPayment 382 ≤ initialValue ((point lo 4 1024 382+point lo 4 1024 383)/2)
    have hp : initialPayment 382 = (172044876096:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 382+point lo 4 1024 383)/2 = (153270673:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153270673:ℝ)/42188800) = (13588480:ℝ)/11741923 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_382
  · change initialPayment 383 ≤ initialValue ((point lo 4 1024 383+point lo 4 1024 384)/2)
    have hp : initialPayment 383 = (172573711346:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 383+point lo 4 1024 384)/2 = (153294811:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153294811:ℝ)/42188800) = (67942400:ℝ)/58685477 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_383
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_023
