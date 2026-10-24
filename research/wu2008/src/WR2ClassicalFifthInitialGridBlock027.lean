import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints027
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_027 (j : Fin 16) : initialPayment (16*27+j.val) ≤
    initialValue ((point lo 4 1024 (16*27+j.val)+point lo 4 1024 (16*27+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 432 ≤ initialValue ((point lo 4 1024 432+point lo 4 1024 433)/2)
    have hp : initialPayment 432 = (199049982309:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 432+point lo 4 1024 433)/2 = (154477573:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154477573:ℝ)/42188800) = (13588480:ℝ)/11500543 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_432
  · change initialPayment 433 ≤ initialValue ((point lo 4 1024 433+point lo 4 1024 434)/2)
    have hp : initialPayment 433 = (199601974782:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 433+point lo 4 1024 434)/2 = (154501711:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154501711:ℝ)/42188800) = (67942400:ℝ)/57478577 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_433
  · change initialPayment 434 ≤ initialValue ((point lo 4 1024 434+point lo 4 1024 435)/2)
    have hp : initialPayment 434 = (200154440342:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 434+point lo 4 1024 435)/2 = (154525849:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154525849:ℝ)/42188800) = (67942400:ℝ)/57454439 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_434
  · change initialPayment 435 ≤ initialValue ((point lo 4 1024 435+point lo 4 1024 436)/2)
    have hp : initialPayment 435 = (200707379387:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 435+point lo 4 1024 436)/2 = (154549987:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154549987:ℝ)/42188800) = (67942400:ℝ)/57430301 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_435
  · change initialPayment 436 ≤ initialValue ((point lo 4 1024 436+point lo 4 1024 437)/2)
    have hp : initialPayment 436 = (201260792318:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 436+point lo 4 1024 437)/2 = (6182965:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6182965:ℝ)/1687552) = (67942400:ℝ)/57406163 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_436
  · change initialPayment 437 ≤ initialValue ((point lo 4 1024 437+point lo 4 1024 438)/2)
    have hp : initialPayment 437 = (201814679536:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 437+point lo 4 1024 438)/2 = (154598263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154598263:ℝ)/42188800) = (2717696:ℝ)/2295281 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_437
  · change initialPayment 438 ≤ initialValue ((point lo 4 1024 438+point lo 4 1024 439)/2)
    have hp : initialPayment 438 = (202369041443:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 438+point lo 4 1024 439)/2 = (154622401:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154622401:ℝ)/42188800) = (67942400:ℝ)/57357887 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_438
  · change initialPayment 439 ≤ initialValue ((point lo 4 1024 439+point lo 4 1024 440)/2)
    have hp : initialPayment 439 = (202923878441:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 439+point lo 4 1024 440)/2 = (154646539:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154646539:ℝ)/42188800) = (67942400:ℝ)/57333749 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_439
  · change initialPayment 440 ≤ initialValue ((point lo 4 1024 440+point lo 4 1024 441)/2)
    have hp : initialPayment 440 = (203479190933:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 440+point lo 4 1024 441)/2 = (154670677:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154670677:ℝ)/42188800) = (67942400:ℝ)/57309611 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_440
  · change initialPayment 441 ≤ initialValue ((point lo 4 1024 441+point lo 4 1024 442)/2)
    have hp : initialPayment 441 = (204034979322:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 441+point lo 4 1024 442)/2 = (30938963:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30938963:ℝ)/8437760) = (67942400:ℝ)/57285473 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_441
  · change initialPayment 442 ≤ initialValue ((point lo 4 1024 442+point lo 4 1024 443)/2)
    have hp : initialPayment 442 = (204591244012:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 442+point lo 4 1024 443)/2 = (154718953:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154718953:ℝ)/42188800) = (13588480:ℝ)/11452267 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_442
  · change initialPayment 443 ≤ initialValue ((point lo 4 1024 443+point lo 4 1024 444)/2)
    have hp : initialPayment 443 = (205147985407:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 443+point lo 4 1024 444)/2 = (154743091:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154743091:ℝ)/42188800) = (67942400:ℝ)/57237197 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_443
  · change initialPayment 444 ≤ initialValue ((point lo 4 1024 444+point lo 4 1024 445)/2)
    have hp : initialPayment 444 = (205705203913:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 444+point lo 4 1024 445)/2 = (154767229:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154767229:ℝ)/42188800) = (67942400:ℝ)/57213059 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_444
  · change initialPayment 445 ≤ initialValue ((point lo 4 1024 445+point lo 4 1024 446)/2)
    have hp : initialPayment 445 = (206262899936:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 445+point lo 4 1024 446)/2 = (154791367:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154791367:ℝ)/42188800) = (67942400:ℝ)/57188921 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_445
  · change initialPayment 446 ≤ initialValue ((point lo 4 1024 446+point lo 4 1024 447)/2)
    have hp : initialPayment 446 = (206821073881:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 446+point lo 4 1024 447)/2 = (30963101:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((30963101:ℝ)/8437760) = (67942400:ℝ)/57164783 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_446
  · change initialPayment 447 ≤ initialValue ((point lo 4 1024 447+point lo 4 1024 448)/2)
    have hp : initialPayment 447 = (207379726155:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 447+point lo 4 1024 448)/2 = (154839643:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((154839643:ℝ)/42188800) = (13588480:ℝ)/11428129 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_447
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_027
