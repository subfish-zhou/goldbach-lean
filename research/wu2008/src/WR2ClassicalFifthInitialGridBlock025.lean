import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints025
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_025 (j : Fin 16) : initialPayment (16*25+j.val) ≤
    initialValue ((point lo 4 1024 (16*25+j.val)+point lo 4 1024 (16*25+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 400 ≤ initialValue ((point lo 4 1024 400+point lo 4 1024 401)/2)
    have hp : initialPayment 400 = (181633650405:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 400+point lo 4 1024 401)/2 = (153705157:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153705157:ℝ)/42188800) = (67942400:ℝ)/58275131 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_400
  · change initialPayment 401 ≤ initialValue ((point lo 4 1024 401+point lo 4 1024 402)/2)
    have hp : initialPayment 401 = (182170711770:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 401+point lo 4 1024 402)/2 = (30745859:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30745859:ℝ)/8437760) = (67942400:ℝ)/58250993 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_401
  · change initialPayment 402 ≤ initialValue ((point lo 4 1024 402+point lo 4 1024 403)/2)
    have hp : initialPayment 402 = (182708233732:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 402+point lo 4 1024 403)/2 = (153753433:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153753433:ℝ)/42188800) = (13588480:ℝ)/11645371 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_402
  · change initialPayment 403 ≤ initialValue ((point lo 4 1024 403+point lo 4 1024 404)/2)
    have hp : initialPayment 403 = (183246216670:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 403+point lo 4 1024 404)/2 = (153777571:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153777571:ℝ)/42188800) = (67942400:ℝ)/58202717 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_403
  · change initialPayment 404 ≤ initialValue ((point lo 4 1024 404+point lo 4 1024 405)/2)
    have hp : initialPayment 404 = (183784660969:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 404+point lo 4 1024 405)/2 = (153801709:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153801709:ℝ)/42188800) = (67942400:ℝ)/58178579 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_404
  · change initialPayment 405 ≤ initialValue ((point lo 4 1024 405+point lo 4 1024 406)/2)
    have hp : initialPayment 405 = (184323567009:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 405+point lo 4 1024 406)/2 = (153825847:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153825847:ℝ)/42188800) = (67942400:ℝ)/58154441 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_405
  · change initialPayment 406 ≤ initialValue ((point lo 4 1024 406+point lo 4 1024 407)/2)
    have hp : initialPayment 406 = (184862935175:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 406+point lo 4 1024 407)/2 = (30769997:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30769997:ℝ)/8437760) = (67942400:ℝ)/58130303 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_406
  · change initialPayment 407 ≤ initialValue ((point lo 4 1024 407+point lo 4 1024 408)/2)
    have hp : initialPayment 407 = (185402765850:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 407+point lo 4 1024 408)/2 = (153874123:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153874123:ℝ)/42188800) = (13588480:ℝ)/11621233 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_407
  · change initialPayment 408 ≤ initialValue ((point lo 4 1024 408+point lo 4 1024 409)/2)
    have hp : initialPayment 408 = (185943059419:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 408+point lo 4 1024 409)/2 = (153898261:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153898261:ℝ)/42188800) = (67942400:ℝ)/58082027 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_408
  · change initialPayment 409 ≤ initialValue ((point lo 4 1024 409+point lo 4 1024 410)/2)
    have hp : initialPayment 409 = (186483816266:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 409+point lo 4 1024 410)/2 = (153922399:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153922399:ℝ)/42188800) = (67942400:ℝ)/58057889 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_409
  · change initialPayment 410 ≤ initialValue ((point lo 4 1024 410+point lo 4 1024 411)/2)
    have hp : initialPayment 410 = (187025036777:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 410+point lo 4 1024 411)/2 = (153946537:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153946537:ℝ)/42188800) = (67942400:ℝ)/58033751 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_410
  · change initialPayment 411 ≤ initialValue ((point lo 4 1024 411+point lo 4 1024 412)/2)
    have hp : initialPayment 411 = (187566721338:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 411+point lo 4 1024 412)/2 = (6158827:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6158827:ℝ)/1687552) = (67942400:ℝ)/58009613 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_411
  · change initialPayment 412 ≤ initialValue ((point lo 4 1024 412+point lo 4 1024 413)/2)
    have hp : initialPayment 412 = (188108870335:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 412+point lo 4 1024 413)/2 = (153994813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((153994813:ℝ)/42188800) = (2717696:ℝ)/2319419 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_412
  · change initialPayment 413 ≤ initialValue ((point lo 4 1024 413+point lo 4 1024 414)/2)
    have hp : initialPayment 413 = (188651484155:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 413+point lo 4 1024 414)/2 = (154018951:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154018951:ℝ)/42188800) = (67942400:ℝ)/57961337 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_413
  · change initialPayment 414 ≤ initialValue ((point lo 4 1024 414+point lo 4 1024 415)/2)
    have hp : initialPayment 414 = (189194563187:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 414+point lo 4 1024 415)/2 = (154043089:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154043089:ℝ)/42188800) = (67942400:ℝ)/57937199 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_414
  · change initialPayment 415 ≤ initialValue ((point lo 4 1024 415+point lo 4 1024 416)/2)
    have hp : initialPayment 415 = (189738107819:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 415+point lo 4 1024 416)/2 = (154067227:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154067227:ℝ)/42188800) = (67942400:ℝ)/57913061 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_415
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_025
