import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints060
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_060 (j : Fin 16) : initialPayment (16*60+j.val) ≤
    initialValue ((point lo 4 1024 (16*60+j.val)+point lo 4 1024 (16*60+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 960 ≤ initialValue ((point lo 4 1024 960+point lo 4 1024 961)/2)
    have hp : initialPayment 960 = (568319275588:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 960+point lo 4 1024 961)/2 = (167222437:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167222437:ℝ)/42188800) = (67942400:ℝ)/44757851 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_960
  · change initialPayment 961 ≤ initialValue ((point lo 4 1024 961+point lo 4 1024 962)/2)
    have hp : initialPayment 961 = (569194656159:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 961+point lo 4 1024 962)/2 = (6689863:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6689863:ℝ)/1687552) = (67942400:ℝ)/44733713 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_961
  · change initialPayment 962 ≤ initialValue ((point lo 4 1024 962+point lo 4 1024 963)/2)
    have hp : initialPayment 962 = (570070832458:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 962+point lo 4 1024 963)/2 = (167270713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167270713:ℝ)/42188800) = (2717696:ℝ)/1788383 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_962
  · change initialPayment 963 ≤ initialValue ((point lo 4 1024 963+point lo 4 1024 964)/2)
    have hp : initialPayment 963 = (570947805385:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 963+point lo 4 1024 964)/2 = (167294851:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167294851:ℝ)/42188800) = (67942400:ℝ)/44685437 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_963
  · change initialPayment 964 ≤ initialValue ((point lo 4 1024 964+point lo 4 1024 965)/2)
    have hp : initialPayment 964 = (571825575845:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 964+point lo 4 1024 965)/2 = (167318989:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167318989:ℝ)/42188800) = (67942400:ℝ)/44661299 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_964
  · change initialPayment 965 ≤ initialValue ((point lo 4 1024 965+point lo 4 1024 966)/2)
    have hp : initialPayment 965 = (572704144740:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 965+point lo 4 1024 966)/2 = (167343127:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167343127:ℝ)/42188800) = (67942400:ℝ)/44637161 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_965
  · change initialPayment 966 ≤ initialValue ((point lo 4 1024 966+point lo 4 1024 967)/2)
    have hp : initialPayment 966 = (573583512977:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 966+point lo 4 1024 967)/2 = (33473453:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33473453:ℝ)/8437760) = (67942400:ℝ)/44613023 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_966
  · change initialPayment 967 ≤ initialValue ((point lo 4 1024 967+point lo 4 1024 968)/2)
    have hp : initialPayment 967 = (574463681462:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 967+point lo 4 1024 968)/2 = (167391403:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167391403:ℝ)/42188800) = (13588480:ℝ)/8917777 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_967
  · change initialPayment 968 ≤ initialValue ((point lo 4 1024 968+point lo 4 1024 969)/2)
    have hp : initialPayment 968 = (575344651106:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 968+point lo 4 1024 969)/2 = (167415541:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167415541:ℝ)/42188800) = (67942400:ℝ)/44564747 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_968
  · change initialPayment 969 ≤ initialValue ((point lo 4 1024 969+point lo 4 1024 970)/2)
    have hp : initialPayment 969 = (576226422818:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 969+point lo 4 1024 970)/2 = (167439679:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167439679:ℝ)/42188800) = (67942400:ℝ)/44540609 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_969
  · change initialPayment 970 ≤ initialValue ((point lo 4 1024 970+point lo 4 1024 971)/2)
    have hp : initialPayment 970 = (577108997509:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 970+point lo 4 1024 971)/2 = (167463817:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167463817:ℝ)/42188800) = (67942400:ℝ)/44516471 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_970
  · change initialPayment 971 ≤ initialValue ((point lo 4 1024 971+point lo 4 1024 972)/2)
    have hp : initialPayment 971 = (577992376094:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 971+point lo 4 1024 972)/2 = (33497591:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33497591:ℝ)/8437760) = (67942400:ℝ)/44492333 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_971
  · change initialPayment 972 ≤ initialValue ((point lo 4 1024 972+point lo 4 1024 973)/2)
    have hp : initialPayment 972 = (578876559487:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 972+point lo 4 1024 973)/2 = (1626331:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((1626331:ℝ)/409600) = (13588480:ℝ)/8893639 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_972
  · change initialPayment 973 ≤ initialValue ((point lo 4 1024 973+point lo 4 1024 974)/2)
    have hp : initialPayment 973 = (579761548604:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 973+point lo 4 1024 974)/2 = (167536231:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167536231:ℝ)/42188800) = (67942400:ℝ)/44444057 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_973
  · change initialPayment 974 ≤ initialValue ((point lo 4 1024 974+point lo 4 1024 975)/2)
    have hp : initialPayment 974 = (580647344365:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 974+point lo 4 1024 975)/2 = (167560369:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167560369:ℝ)/42188800) = (67942400:ℝ)/44419919 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_974
  · change initialPayment 975 ≤ initialValue ((point lo 4 1024 975+point lo 4 1024 976)/2)
    have hp : initialPayment 975 = (581533947687:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 975+point lo 4 1024 976)/2 = (167584507:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167584507:ℝ)/42188800) = (67942400:ℝ)/44395781 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_975
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_060
