import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints021
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_021 (j : Fin 16) : initialPayment (16*21+j.val) ≤
    initialValue ((point lo 4 1024 (16*21+j.val)+point lo 4 1024 (16*21+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 336 ≤ initialValue ((point lo 4 1024 336+point lo 4 1024 337)/2)
    have hp : initialPayment 336 = (148202722880:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 336+point lo 4 1024 337)/2 = (6086413:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6086413:ℝ)/1687552) = (67942400:ℝ)/59819963 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_336
  · change initialPayment 337 ≤ initialValue ((point lo 4 1024 337+point lo 4 1024 338)/2)
    have hp : initialPayment 337 = (148711074777:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 337+point lo 4 1024 338)/2 = (152184463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152184463:ℝ)/42188800) = (2717696:ℝ)/2391833 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_337
  · change initialPayment 338 ≤ initialValue ((point lo 4 1024 338+point lo 4 1024 339)/2)
    have hp : initialPayment 338 = (149219863975:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 338+point lo 4 1024 339)/2 = (152208601:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152208601:ℝ)/42188800) = (67942400:ℝ)/59771687 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_338
  · change initialPayment 339 ≤ initialValue ((point lo 4 1024 339+point lo 4 1024 340)/2)
    have hp : initialPayment 339 = (149729090823:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 339+point lo 4 1024 340)/2 = (152232739:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152232739:ℝ)/42188800) = (67942400:ℝ)/59747549 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_339
  · change initialPayment 340 ≤ initialValue ((point lo 4 1024 340+point lo 4 1024 341)/2)
    have hp : initialPayment 340 = (150238755668:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 340+point lo 4 1024 341)/2 = (152256877:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152256877:ℝ)/42188800) = (67942400:ℝ)/59723411 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_340
  · change initialPayment 341 ≤ initialValue ((point lo 4 1024 341+point lo 4 1024 342)/2)
    have hp : initialPayment 341 = (150748858859:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 341+point lo 4 1024 342)/2 = (30456203:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30456203:ℝ)/8437760) = (67942400:ℝ)/59699273 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_341
  · change initialPayment 342 ≤ initialValue ((point lo 4 1024 342+point lo 4 1024 343)/2)
    have hp : initialPayment 342 = (151259400745:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 342+point lo 4 1024 343)/2 = (152305153:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152305153:ℝ)/42188800) = (13588480:ℝ)/11935027 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_342
  · change initialPayment 343 ≤ initialValue ((point lo 4 1024 343+point lo 4 1024 344)/2)
    have hp : initialPayment 343 = (151770381675:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 343+point lo 4 1024 344)/2 = (152329291:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152329291:ℝ)/42188800) = (67942400:ℝ)/59650997 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_343
  · change initialPayment 344 ≤ initialValue ((point lo 4 1024 344+point lo 4 1024 345)/2)
    have hp : initialPayment 344 = (152281801999:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 344+point lo 4 1024 345)/2 = (152353429:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152353429:ℝ)/42188800) = (67942400:ℝ)/59626859 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_344
  · change initialPayment 345 ≤ initialValue ((point lo 4 1024 345+point lo 4 1024 346)/2)
    have hp : initialPayment 345 = (152793662068:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 345+point lo 4 1024 346)/2 = (152377567:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152377567:ℝ)/42188800) = (67942400:ℝ)/59602721 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_345
  · change initialPayment 346 ≤ initialValue ((point lo 4 1024 346+point lo 4 1024 347)/2)
    have hp : initialPayment 346 = (153305962233:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 346+point lo 4 1024 347)/2 = (30480341:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30480341:ℝ)/8437760) = (67942400:ℝ)/59578583 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_346
  · change initialPayment 347 ≤ initialValue ((point lo 4 1024 347+point lo 4 1024 348)/2)
    have hp : initialPayment 347 = (153818702845:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 347+point lo 4 1024 348)/2 = (152425843:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152425843:ℝ)/42188800) = (13588480:ℝ)/11910889 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_347
  · change initialPayment 348 ≤ initialValue ((point lo 4 1024 348+point lo 4 1024 349)/2)
    have hp : initialPayment 348 = (154331884257:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 348+point lo 4 1024 349)/2 = (152449981:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152449981:ℝ)/42188800) = (67942400:ℝ)/59530307 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_348
  · change initialPayment 349 ≤ initialValue ((point lo 4 1024 349+point lo 4 1024 350)/2)
    have hp : initialPayment 349 = (154845506821:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 349+point lo 4 1024 350)/2 = (152474119:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152474119:ℝ)/42188800) = (67942400:ℝ)/59506169 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_349
  · change initialPayment 350 ≤ initialValue ((point lo 4 1024 350+point lo 4 1024 351)/2)
    have hp : initialPayment 350 = (155359570891:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 350+point lo 4 1024 351)/2 = (152498257:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((152498257:ℝ)/42188800) = (67942400:ℝ)/59482031 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_350
  · change initialPayment 351 ≤ initialValue ((point lo 4 1024 351+point lo 4 1024 352)/2)
    have hp : initialPayment 351 = (155874076819:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 351+point lo 4 1024 352)/2 = (30504479:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30504479:ℝ)/8437760) = (67942400:ℝ)/59457893 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_351
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_021
