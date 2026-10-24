import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints056
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_056 (j : Fin 16) : initialPayment (16*56+j.val) ≤
    initialValue ((point lo 4 1024 (16*56+j.val)+point lo 4 1024 (16*56+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 896 ≤ initialValue ((point lo 4 1024 896+point lo 4 1024 897)/2)
    have hp : initialPayment 896 = (513909908573:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 896+point lo 4 1024 897)/2 = (33135521:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33135521:ℝ)/8437760) = (67942400:ℝ)/46302683 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_896
  · change initialPayment 897 ≤ initialValue ((point lo 4 1024 897+point lo 4 1024 898)/2)
    have hp : initialPayment 897 = (514736170875:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 897+point lo 4 1024 898)/2 = (165701743:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165701743:ℝ)/42188800) = (13588480:ℝ)/9255709 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_897
  · change initialPayment 898 ≤ initialValue ((point lo 4 1024 898+point lo 4 1024 899)/2)
    have hp : initialPayment 898 = (515563174207:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 898+point lo 4 1024 899)/2 = (165725881:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165725881:ℝ)/42188800) = (67942400:ℝ)/46254407 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_898
  · change initialPayment 899 ≤ initialValue ((point lo 4 1024 899+point lo 4 1024 900)/2)
    have hp : initialPayment 899 = (516390919381:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 899+point lo 4 1024 900)/2 = (165750019:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165750019:ℝ)/42188800) = (67942400:ℝ)/46230269 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_899
  · change initialPayment 900 ≤ initialValue ((point lo 4 1024 900+point lo 4 1024 901)/2)
    have hp : initialPayment 900 = (517219407210:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 900+point lo 4 1024 901)/2 = (165774157:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165774157:ℝ)/42188800) = (67942400:ℝ)/46206131 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_900
  · change initialPayment 901 ≤ initialValue ((point lo 4 1024 901+point lo 4 1024 902)/2)
    have hp : initialPayment 901 = (518048638507:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 901+point lo 4 1024 902)/2 = (33159659:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33159659:ℝ)/8437760) = (67942400:ℝ)/46181993 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_901
  · change initialPayment 902 ≤ initialValue ((point lo 4 1024 902+point lo 4 1024 903)/2)
    have hp : initialPayment 902 = (518878614089:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 902+point lo 4 1024 903)/2 = (165822433:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165822433:ℝ)/42188800) = (13588480:ℝ)/9231571 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_902
  · change initialPayment 903 ≤ initialValue ((point lo 4 1024 903+point lo 4 1024 904)/2)
    have hp : initialPayment 903 = (519709334771:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 903+point lo 4 1024 904)/2 = (165846571:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165846571:ℝ)/42188800) = (67942400:ℝ)/46133717 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_903
  · change initialPayment 904 ≤ initialValue ((point lo 4 1024 904+point lo 4 1024 905)/2)
    have hp : initialPayment 904 = (520540801372:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 904+point lo 4 1024 905)/2 = (165870709:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165870709:ℝ)/42188800) = (67942400:ℝ)/46109579 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_904
  · change initialPayment 905 ≤ initialValue ((point lo 4 1024 905+point lo 4 1024 906)/2)
    have hp : initialPayment 905 = (521373014710:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 905+point lo 4 1024 906)/2 = (165894847:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165894847:ℝ)/42188800) = (67942400:ℝ)/46085441 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_905
  · change initialPayment 906 ≤ initialValue ((point lo 4 1024 906+point lo 4 1024 907)/2)
    have hp : initialPayment 906 = (522205975607:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 906+point lo 4 1024 907)/2 = (33183797:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33183797:ℝ)/8437760) = (67942400:ℝ)/46061303 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_906
  · change initialPayment 907 ≤ initialValue ((point lo 4 1024 907+point lo 4 1024 908)/2)
    have hp : initialPayment 907 = (523039684885:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 907+point lo 4 1024 908)/2 = (165943123:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165943123:ℝ)/42188800) = (13588480:ℝ)/9207433 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_907
  · change initialPayment 908 ≤ initialValue ((point lo 4 1024 908+point lo 4 1024 909)/2)
    have hp : initialPayment 908 = (523874143366:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 908+point lo 4 1024 909)/2 = (165967261:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165967261:ℝ)/42188800) = (67942400:ℝ)/46013027 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_908
  · change initialPayment 909 ≤ initialValue ((point lo 4 1024 909+point lo 4 1024 910)/2)
    have hp : initialPayment 909 = (524709351876:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 909+point lo 4 1024 910)/2 = (165991399:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((165991399:ℝ)/42188800) = (67942400:ℝ)/45988889 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_909
  · change initialPayment 910 ≤ initialValue ((point lo 4 1024 910+point lo 4 1024 911)/2)
    have hp : initialPayment 910 = (525545311240:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 910+point lo 4 1024 911)/2 = (166015537:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166015537:ℝ)/42188800) = (67942400:ℝ)/45964751 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_910
  · change initialPayment 911 ≤ initialValue ((point lo 4 1024 911+point lo 4 1024 912)/2)
    have hp : initialPayment 911 = (526382022286:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 911+point lo 4 1024 912)/2 = (6641587:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6641587:ℝ)/1687552) = (67942400:ℝ)/45940613 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_911
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_056
