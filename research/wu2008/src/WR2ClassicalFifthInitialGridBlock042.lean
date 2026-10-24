import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints042
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_042 (j : Fin 16) : initialPayment (16*42+j.val) ≤
    initialValue ((point lo 4 1024 (16*42+j.val)+point lo 4 1024 (16*42+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 672 ≤ initialValue ((point lo 4 1024 672+point lo 4 1024 673)/2)
    have hp : initialPayment 672 = (346091180851:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 672+point lo 4 1024 673)/2 = (160270693:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160270693:ℝ)/42188800) = (13588480:ℝ)/10341919 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_672
  · change initialPayment 673 ≤ initialValue ((point lo 4 1024 673+point lo 4 1024 674)/2)
    have hp : initialPayment 673 = (346769647996:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 673+point lo 4 1024 674)/2 = (160294831:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160294831:ℝ)/42188800) = (67942400:ℝ)/51685457 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_673
  · change initialPayment 674 ≤ initialValue ((point lo 4 1024 674+point lo 4 1024 675)/2)
    have hp : initialPayment 674 = (347448703315:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 674+point lo 4 1024 675)/2 = (160318969:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160318969:ℝ)/42188800) = (67942400:ℝ)/51661319 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_674
  · change initialPayment 675 ≤ initialValue ((point lo 4 1024 675+point lo 4 1024 676)/2)
    have hp : initialPayment 675 = (348128347381:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 675+point lo 4 1024 676)/2 = (160343107:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160343107:ℝ)/42188800) = (67942400:ℝ)/51637181 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_675
  · change initialPayment 676 ≤ initialValue ((point lo 4 1024 676+point lo 4 1024 677)/2)
    have hp : initialPayment 676 = (348808580764:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 676+point lo 4 1024 677)/2 = (32073449:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32073449:ℝ)/8437760) = (67942400:ℝ)/51613043 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_676
  · change initialPayment 677 ≤ initialValue ((point lo 4 1024 677+point lo 4 1024 678)/2)
    have hp : initialPayment 677 = (349489404039:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 677+point lo 4 1024 678)/2 = (160391383:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160391383:ℝ)/42188800) = (13588480:ℝ)/10317781 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_677
  · change initialPayment 678 ≤ initialValue ((point lo 4 1024 678+point lo 4 1024 679)/2)
    have hp : initialPayment 678 = (350170817778:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 678+point lo 4 1024 679)/2 = (160415521:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160415521:ℝ)/42188800) = (67942400:ℝ)/51564767 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_678
  · change initialPayment 679 ≤ initialValue ((point lo 4 1024 679+point lo 4 1024 680)/2)
    have hp : initialPayment 679 = (350852822556:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 679+point lo 4 1024 680)/2 = (160439659:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160439659:ℝ)/42188800) = (67942400:ℝ)/51540629 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_679
  · change initialPayment 680 ≤ initialValue ((point lo 4 1024 680+point lo 4 1024 681)/2)
    have hp : initialPayment 680 = (351535418950:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 680+point lo 4 1024 681)/2 = (160463797:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160463797:ℝ)/42188800) = (67942400:ℝ)/51516491 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_680
  · change initialPayment 681 ≤ initialValue ((point lo 4 1024 681+point lo 4 1024 682)/2)
    have hp : initialPayment 681 = (352218607535:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 681+point lo 4 1024 682)/2 = (32097587:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32097587:ℝ)/8437760) = (67942400:ℝ)/51492353 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_681
  · change initialPayment 682 ≤ initialValue ((point lo 4 1024 682+point lo 4 1024 683)/2)
    have hp : initialPayment 682 = (352902388888:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 682+point lo 4 1024 683)/2 = (160512073:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160512073:ℝ)/42188800) = (13588480:ℝ)/10293643 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_682
  · change initialPayment 683 ≤ initialValue ((point lo 4 1024 683+point lo 4 1024 684)/2)
    have hp : initialPayment 683 = (353586763589:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 683+point lo 4 1024 684)/2 = (160536211:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160536211:ℝ)/42188800) = (67942400:ℝ)/51444077 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_683
  · change initialPayment 684 ≤ initialValue ((point lo 4 1024 684+point lo 4 1024 685)/2)
    have hp : initialPayment 684 = (354271732215:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 684+point lo 4 1024 685)/2 = (160560349:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160560349:ℝ)/42188800) = (67942400:ℝ)/51419939 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_684
  · change initialPayment 685 ≤ initialValue ((point lo 4 1024 685+point lo 4 1024 686)/2)
    have hp : initialPayment 685 = (354957295348:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 685+point lo 4 1024 686)/2 = (160584487:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160584487:ℝ)/42188800) = (67942400:ℝ)/51395801 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_685
  · change initialPayment 686 ≤ initialValue ((point lo 4 1024 686+point lo 4 1024 687)/2)
    have hp : initialPayment 686 = (355643453567:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 686+point lo 4 1024 687)/2 = (6424345:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6424345:ℝ)/1687552) = (67942400:ℝ)/51371663 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_686
  · change initialPayment 687 ≤ initialValue ((point lo 4 1024 687+point lo 4 1024 688)/2)
    have hp : initialPayment 687 = (356330207455:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 687+point lo 4 1024 688)/2 = (160632763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160632763:ℝ)/42188800) = (2717696:ℝ)/2053901 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_687
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_042
