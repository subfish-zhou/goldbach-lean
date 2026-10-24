import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints062
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_062 (j : Fin 16) : initialPayment (16*62+j.val) ≤
    initialValue ((point lo 4 1024 (16*62+j.val)+point lo 4 1024 (16*62+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 992 ≤ initialValue ((point lo 4 1024 992+point lo 4 1024 993)/2)
    have hp : initialPayment 992 = (596730659617:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 992+point lo 4 1024 993)/2 = (167994853:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167994853:ℝ)/42188800) = (13588480:ℝ)/8797087 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_992
  · change initialPayment 993 ≤ initialValue ((point lo 4 1024 993+point lo 4 1024 994)/2)
    have hp : initialPayment 993 = (597631958053:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 993+point lo 4 1024 994)/2 = (168018991:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168018991:ℝ)/42188800) = (67942400:ℝ)/43961297 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_993
  · change initialPayment 994 ≤ initialValue ((point lo 4 1024 994+point lo 4 1024 995)/2)
    have hp : initialPayment 994 = (598534081818:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 994+point lo 4 1024 995)/2 = (168043129:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168043129:ℝ)/42188800) = (67942400:ℝ)/43937159 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_994
  · change initialPayment 995 ≤ initialValue ((point lo 4 1024 995+point lo 4 1024 996)/2)
    have hp : initialPayment 995 = (599437031861:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 995+point lo 4 1024 996)/2 = (168067267:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168067267:ℝ)/42188800) = (67942400:ℝ)/43913021 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_995
  · change initialPayment 996 ≤ initialValue ((point lo 4 1024 996+point lo 4 1024 997)/2)
    have hp : initialPayment 996 = (600340809135:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 996+point lo 4 1024 997)/2 = (33618281:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33618281:ℝ)/8437760) = (67942400:ℝ)/43888883 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_996
  · change initialPayment 997 ≤ initialValue ((point lo 4 1024 997+point lo 4 1024 998)/2)
    have hp : initialPayment 997 = (601245414594:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 997+point lo 4 1024 998)/2 = (168115543:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168115543:ℝ)/42188800) = (13588480:ℝ)/8772949 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_997
  · change initialPayment 998 ≤ initialValue ((point lo 4 1024 998+point lo 4 1024 999)/2)
    have hp : initialPayment 998 = (602150849194:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 998+point lo 4 1024 999)/2 = (168139681:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168139681:ℝ)/42188800) = (67942400:ℝ)/43840607 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_998
  · change initialPayment 999 ≤ initialValue ((point lo 4 1024 999+point lo 4 1024 1000)/2)
    have hp : initialPayment 999 = (603057113892:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 999+point lo 4 1024 1000)/2 = (168163819:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168163819:ℝ)/42188800) = (67942400:ℝ)/43816469 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_999
  · change initialPayment 1000 ≤ initialValue ((point lo 4 1024 1000+point lo 4 1024 1001)/2)
    have hp : initialPayment 1000 = (603964209646:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1000+point lo 4 1024 1001)/2 = (168187957:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168187957:ℝ)/42188800) = (67942400:ℝ)/43792331 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1000
  · change initialPayment 1001 ≤ initialValue ((point lo 4 1024 1001+point lo 4 1024 1002)/2)
    have hp : initialPayment 1001 = (604872137419:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1001+point lo 4 1024 1002)/2 = (33642419:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33642419:ℝ)/8437760) = (67942400:ℝ)/43768193 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1001
  · change initialPayment 1002 ≤ initialValue ((point lo 4 1024 1002+point lo 4 1024 1003)/2)
    have hp : initialPayment 1002 = (605780898171:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1002+point lo 4 1024 1003)/2 = (168236233:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168236233:ℝ)/42188800) = (13588480:ℝ)/8748811 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1002
  · change initialPayment 1003 ≤ initialValue ((point lo 4 1024 1003+point lo 4 1024 1004)/2)
    have hp : initialPayment 1003 = (606690492866:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1003+point lo 4 1024 1004)/2 = (168260371:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168260371:ℝ)/42188800) = (67942400:ℝ)/43719917 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1003
  · change initialPayment 1004 ≤ initialValue ((point lo 4 1024 1004+point lo 4 1024 1005)/2)
    have hp : initialPayment 1004 = (607600922470:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1004+point lo 4 1024 1005)/2 = (168284509:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168284509:ℝ)/42188800) = (67942400:ℝ)/43695779 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1004
  · change initialPayment 1005 ≤ initialValue ((point lo 4 1024 1005+point lo 4 1024 1006)/2)
    have hp : initialPayment 1005 = (608512187950:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1005+point lo 4 1024 1006)/2 = (168308647:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168308647:ℝ)/42188800) = (67942400:ℝ)/43671641 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1005
  · change initialPayment 1006 ≤ initialValue ((point lo 4 1024 1006+point lo 4 1024 1007)/2)
    have hp : initialPayment 1006 = (609424290274:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1006+point lo 4 1024 1007)/2 = (33666557:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33666557:ℝ)/8437760) = (67942400:ℝ)/43647503 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1006
  · change initialPayment 1007 ≤ initialValue ((point lo 4 1024 1007+point lo 4 1024 1008)/2)
    have hp : initialPayment 1007 = (610337230413:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1007+point lo 4 1024 1008)/2 = (168356923:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((168356923:ℝ)/42188800) = (13588480:ℝ)/8724673 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1007
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_062
