import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints047
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_047 (j : Fin 16) : initialPayment (16*47+j.val) ≤
    initialValue ((point lo 4 1024 (16*47+j.val)+point lo 4 1024 (16*47+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 752 ≤ initialValue ((point lo 4 1024 752+point lo 4 1024 753)/2)
    have hp : initialPayment 752 = (402275525019:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 752+point lo 4 1024 753)/2 = (162201733:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162201733:ℝ)/42188800) = (13588480:ℝ)/9955711 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_752
  · change initialPayment 753 ≤ initialValue ((point lo 4 1024 753+point lo 4 1024 754)/2)
    have hp : initialPayment 753 = (403002924956:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 753+point lo 4 1024 754)/2 = (162225871:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162225871:ℝ)/42188800) = (67942400:ℝ)/49754417 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_753
  · change initialPayment 754 ≤ initialValue ((point lo 4 1024 754+point lo 4 1024 755)/2)
    have hp : initialPayment 754 = (403730961639:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 754+point lo 4 1024 755)/2 = (162250009:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162250009:ℝ)/42188800) = (67942400:ℝ)/49730279 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_754
  · change initialPayment 755 ≤ initialValue ((point lo 4 1024 755+point lo 4 1024 756)/2)
    have hp : initialPayment 755 = (404459635712:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 755+point lo 4 1024 756)/2 = (162274147:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162274147:ℝ)/42188800) = (67942400:ℝ)/49706141 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_755
  · change initialPayment 756 ≤ initialValue ((point lo 4 1024 756+point lo 4 1024 757)/2)
    have hp : initialPayment 756 = (405188947823:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 756+point lo 4 1024 757)/2 = (32459657:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32459657:ℝ)/8437760) = (67942400:ℝ)/49682003 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_756
  · change initialPayment 757 ≤ initialValue ((point lo 4 1024 757+point lo 4 1024 758)/2)
    have hp : initialPayment 757 = (405918898620:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 757+point lo 4 1024 758)/2 = (162322423:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162322423:ℝ)/42188800) = (13588480:ℝ)/9931573 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_757
  · change initialPayment 758 ≤ initialValue ((point lo 4 1024 758+point lo 4 1024 759)/2)
    have hp : initialPayment 758 = (406649488750:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 758+point lo 4 1024 759)/2 = (162346561:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162346561:ℝ)/42188800) = (67942400:ℝ)/49633727 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_758
  · change initialPayment 759 ≤ initialValue ((point lo 4 1024 759+point lo 4 1024 760)/2)
    have hp : initialPayment 759 = (407380718865:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 759+point lo 4 1024 760)/2 = (162370699:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162370699:ℝ)/42188800) = (67942400:ℝ)/49609589 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_759
  · change initialPayment 760 ≤ initialValue ((point lo 4 1024 760+point lo 4 1024 761)/2)
    have hp : initialPayment 760 = (408112589615:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 760+point lo 4 1024 761)/2 = (162394837:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162394837:ℝ)/42188800) = (67942400:ℝ)/49585451 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_760
  · change initialPayment 761 ≤ initialValue ((point lo 4 1024 761+point lo 4 1024 762)/2)
    have hp : initialPayment 761 = (408845101651:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 761+point lo 4 1024 762)/2 = (6496759:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6496759:ℝ)/1687552) = (67942400:ℝ)/49561313 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_761
  · change initialPayment 762 ≤ initialValue ((point lo 4 1024 762+point lo 4 1024 763)/2)
    have hp : initialPayment 762 = (409578255627:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 762+point lo 4 1024 763)/2 = (162443113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162443113:ℝ)/42188800) = (2717696:ℝ)/1981487 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_762
  · change initialPayment 763 ≤ initialValue ((point lo 4 1024 763+point lo 4 1024 764)/2)
    have hp : initialPayment 763 = (410312052196:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 763+point lo 4 1024 764)/2 = (162467251:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162467251:ℝ)/42188800) = (67942400:ℝ)/49513037 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_763
  · change initialPayment 764 ≤ initialValue ((point lo 4 1024 764+point lo 4 1024 765)/2)
    have hp : initialPayment 764 = (411046492013:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 764+point lo 4 1024 765)/2 = (162491389:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162491389:ℝ)/42188800) = (67942400:ℝ)/49488899 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_764
  · change initialPayment 765 ≤ initialValue ((point lo 4 1024 765+point lo 4 1024 766)/2)
    have hp : initialPayment 765 = (411781575735:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 765+point lo 4 1024 766)/2 = (162515527:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162515527:ℝ)/42188800) = (67942400:ℝ)/49464761 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_765
  · change initialPayment 766 ≤ initialValue ((point lo 4 1024 766+point lo 4 1024 767)/2)
    have hp : initialPayment 766 = (412517304017:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 766+point lo 4 1024 767)/2 = (315611:ℝ)/81920 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((315611:ℝ)/81920) = (67942400:ℝ)/49440623 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_766
  · change initialPayment 767 ≤ initialValue ((point lo 4 1024 767+point lo 4 1024 768)/2)
    have hp : initialPayment 767 = (413253677518:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 767+point lo 4 1024 768)/2 = (162563803:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162563803:ℝ)/42188800) = (13588480:ℝ)/9883297 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_767
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_047
