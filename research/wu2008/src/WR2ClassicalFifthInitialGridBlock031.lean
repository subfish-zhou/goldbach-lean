import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints031
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_031 (j : Fin 16) : initialPayment (16*31+j.val) ≤
    initialValue ((point lo 4 1024 (16*31+j.val)+point lo 4 1024 (16*31+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 496 ≤ initialValue ((point lo 4 1024 496+point lo 4 1024 497)/2)
    have hp : initialPayment 496 = (235348279166:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 496+point lo 4 1024 497)/2 = (31204481:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31204481:ℝ)/8437760) = (67942400:ℝ)/55957883 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_496
  · change initialPayment 497 ≤ initialValue ((point lo 4 1024 497+point lo 4 1024 498)/2)
    have hp : initialPayment 497 = (235931380169:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 497+point lo 4 1024 498)/2 = (156046543:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156046543:ℝ)/42188800) = (13588480:ℝ)/11186749 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_497
  · change initialPayment 498 ≤ initialValue ((point lo 4 1024 498+point lo 4 1024 499)/2)
    have hp : initialPayment 498 = (236514981065:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 498+point lo 4 1024 499)/2 = (156070681:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156070681:ℝ)/42188800) = (67942400:ℝ)/55909607 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_498
  · change initialPayment 499 ≤ initialValue ((point lo 4 1024 499+point lo 4 1024 500)/2)
    have hp : initialPayment 499 = (237099082294:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 499+point lo 4 1024 500)/2 = (156094819:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156094819:ℝ)/42188800) = (67942400:ℝ)/55885469 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_499
  · change initialPayment 500 ≤ initialValue ((point lo 4 1024 500+point lo 4 1024 501)/2)
    have hp : initialPayment 500 = (237683684297:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 500+point lo 4 1024 501)/2 = (156118957:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156118957:ℝ)/42188800) = (67942400:ℝ)/55861331 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_500
  · change initialPayment 501 ≤ initialValue ((point lo 4 1024 501+point lo 4 1024 502)/2)
    have hp : initialPayment 501 = (238268787513:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 501+point lo 4 1024 502)/2 = (31228619:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31228619:ℝ)/8437760) = (67942400:ℝ)/55837193 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_501
  · change initialPayment 502 ≤ initialValue ((point lo 4 1024 502+point lo 4 1024 503)/2)
    have hp : initialPayment 502 = (238854392384:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 502+point lo 4 1024 503)/2 = (156167233:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156167233:ℝ)/42188800) = (13588480:ℝ)/11162611 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_502
  · change initialPayment 503 ≤ initialValue ((point lo 4 1024 503+point lo 4 1024 504)/2)
    have hp : initialPayment 503 = (239440499351:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 503+point lo 4 1024 504)/2 = (156191371:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156191371:ℝ)/42188800) = (67942400:ℝ)/55788917 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_503
  · change initialPayment 504 ≤ initialValue ((point lo 4 1024 504+point lo 4 1024 505)/2)
    have hp : initialPayment 504 = (240027108858:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 504+point lo 4 1024 505)/2 = (156215509:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156215509:ℝ)/42188800) = (67942400:ℝ)/55764779 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_504
  · change initialPayment 505 ≤ initialValue ((point lo 4 1024 505+point lo 4 1024 506)/2)
    have hp : initialPayment 505 = (240614221346:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 505+point lo 4 1024 506)/2 = (156239647:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156239647:ℝ)/42188800) = (67942400:ℝ)/55740641 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_505
  · change initialPayment 506 ≤ initialValue ((point lo 4 1024 506+point lo 4 1024 507)/2)
    have hp : initialPayment 506 = (241201837260:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 506+point lo 4 1024 507)/2 = (31252757:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31252757:ℝ)/8437760) = (67942400:ℝ)/55716503 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_506
  · change initialPayment 507 ≤ initialValue ((point lo 4 1024 507+point lo 4 1024 508)/2)
    have hp : initialPayment 507 = (241789957045:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 507+point lo 4 1024 508)/2 = (156287923:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156287923:ℝ)/42188800) = (13588480:ℝ)/11138473 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_507
  · change initialPayment 508 ≤ initialValue ((point lo 4 1024 508+point lo 4 1024 509)/2)
    have hp : initialPayment 508 = (242378581144:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 508+point lo 4 1024 509)/2 = (156312061:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156312061:ℝ)/42188800) = (67942400:ℝ)/55668227 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_508
  · change initialPayment 509 ≤ initialValue ((point lo 4 1024 509+point lo 4 1024 510)/2)
    have hp : initialPayment 509 = (242967710005:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 509+point lo 4 1024 510)/2 = (156336199:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156336199:ℝ)/42188800) = (67942400:ℝ)/55644089 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_509
  · change initialPayment 510 ≤ initialValue ((point lo 4 1024 510+point lo 4 1024 511)/2)
    have hp : initialPayment 510 = (243557344073:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 510+point lo 4 1024 511)/2 = (156360337:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((156360337:ℝ)/42188800) = (67942400:ℝ)/55619951 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_510
  · change initialPayment 511 ≤ initialValue ((point lo 4 1024 511+point lo 4 1024 512)/2)
    have hp : initialPayment 511 = (244147483796:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 511+point lo 4 1024 512)/2 = (6255379:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6255379:ℝ)/1687552) = (67942400:ℝ)/55595813 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_511
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_031
