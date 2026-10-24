import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints033
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_033 (j : Fin 16) : initialPayment (16*33+j.val) ≤
    initialValue ((point lo 4 1024 (16*33+j.val)+point lo 4 1024 (16*33+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 528 ≤ initialValue ((point lo 4 1024 528+point lo 4 1024 529)/2)
    have hp : initialPayment 528 = (254257660597:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 528+point lo 4 1024 529)/2 = (156794821:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156794821:ℝ)/42188800) = (67942400:ℝ)/55185467 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_528
  · change initialPayment 529 ≤ initialValue ((point lo 4 1024 529+point lo 4 1024 530)/2)
    have hp : initialPayment 529 = (254856979300:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 529+point lo 4 1024 530)/2 = (156818959:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156818959:ℝ)/42188800) = (67942400:ℝ)/55161329 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_529
  · change initialPayment 530 ≤ initialValue ((point lo 4 1024 530+point lo 4 1024 531)/2)
    have hp : initialPayment 530 = (255456812277:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 530+point lo 4 1024 531)/2 = (156843097:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156843097:ℝ)/42188800) = (67942400:ℝ)/55137191 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_530
  · change initialPayment 531 ≤ initialValue ((point lo 4 1024 531+point lo 4 1024 532)/2)
    have hp : initialPayment 531 = (256057159990:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 531+point lo 4 1024 532)/2 = (31373447:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31373447:ℝ)/8437760) = (67942400:ℝ)/55113053 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_531
  · change initialPayment 532 ≤ initialValue ((point lo 4 1024 532+point lo 4 1024 533)/2)
    have hp : initialPayment 532 = (256658022899:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 532+point lo 4 1024 533)/2 = (156891373:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156891373:ℝ)/42188800) = (13588480:ℝ)/11017783 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_532
  · change initialPayment 533 ≤ initialValue ((point lo 4 1024 533+point lo 4 1024 534)/2)
    have hp : initialPayment 533 = (257259401466:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 533+point lo 4 1024 534)/2 = (156915511:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156915511:ℝ)/42188800) = (67942400:ℝ)/55064777 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_533
  · change initialPayment 534 ≤ initialValue ((point lo 4 1024 534+point lo 4 1024 535)/2)
    have hp : initialPayment 534 = (257861296154:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 534+point lo 4 1024 535)/2 = (156939649:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156939649:ℝ)/42188800) = (67942400:ℝ)/55040639 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_534
  · change initialPayment 535 ≤ initialValue ((point lo 4 1024 535+point lo 4 1024 536)/2)
    have hp : initialPayment 535 = (258463707425:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 535+point lo 4 1024 536)/2 = (156963787:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156963787:ℝ)/42188800) = (67942400:ℝ)/55016501 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_535
  · change initialPayment 536 ≤ initialValue ((point lo 4 1024 536+point lo 4 1024 537)/2)
    have hp : initialPayment 536 = (259066635744:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 536+point lo 4 1024 537)/2 = (6279517:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6279517:ℝ)/1687552) = (67942400:ℝ)/54992363 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_536
  · change initialPayment 537 ≤ initialValue ((point lo 4 1024 537+point lo 4 1024 538)/2)
    have hp : initialPayment 537 = (259670081575:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 537+point lo 4 1024 538)/2 = (157012063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157012063:ℝ)/42188800) = (2717696:ℝ)/2198729 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_537
  · change initialPayment 538 ≤ initialValue ((point lo 4 1024 538+point lo 4 1024 539)/2)
    have hp : initialPayment 538 = (260274045383:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 538+point lo 4 1024 539)/2 = (157036201:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157036201:ℝ)/42188800) = (67942400:ℝ)/54944087 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_538
  · change initialPayment 539 ≤ initialValue ((point lo 4 1024 539+point lo 4 1024 540)/2)
    have hp : initialPayment 539 = (260878527635:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 539+point lo 4 1024 540)/2 = (157060339:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157060339:ℝ)/42188800) = (67942400:ℝ)/54919949 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_539
  · change initialPayment 540 ≤ initialValue ((point lo 4 1024 540+point lo 4 1024 541)/2)
    have hp : initialPayment 540 = (261483528797:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 540+point lo 4 1024 541)/2 = (157084477:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157084477:ℝ)/42188800) = (67942400:ℝ)/54895811 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_540
  · change initialPayment 541 ≤ initialValue ((point lo 4 1024 541+point lo 4 1024 542)/2)
    have hp : initialPayment 541 = (262089049335:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 541+point lo 4 1024 542)/2 = (31421723:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31421723:ℝ)/8437760) = (67942400:ℝ)/54871673 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_541
  · change initialPayment 542 ≤ initialValue ((point lo 4 1024 542+point lo 4 1024 543)/2)
    have hp : initialPayment 542 = (262695089719:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 542+point lo 4 1024 543)/2 = (157132753:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157132753:ℝ)/42188800) = (13588480:ℝ)/10969507 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_542
  · change initialPayment 543 ≤ initialValue ((point lo 4 1024 543+point lo 4 1024 544)/2)
    have hp : initialPayment 543 = (263301650417:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 543+point lo 4 1024 544)/2 = (157156891:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157156891:ℝ)/42188800) = (67942400:ℝ)/54823397 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_543
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_033
