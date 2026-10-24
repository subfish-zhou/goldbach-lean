import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints000
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_000 (j : Fin 16) : initialPayment (16*0+j.val) ≤
    initialValue ((point lo 4 1024 (16*0+j.val)+point lo 4 1024 (16*0+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 0 ≤ initialValue ((point lo 4 1024 0+point lo 4 1024 1)/2)
    have hp : initialPayment 0 = (188968492:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 0+point lo 4 1024 1)/2 = (144049957:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144049957:ℝ)/42188800) = (67942400:ℝ)/67930331 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_0
  · change initialPayment 1 ≤ initialValue ((point lo 4 1024 1+point lo 4 1024 2)/2)
    have hp : initialPayment 1 = (567164369:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 1+point lo 4 1024 2)/2 = (28814819:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((28814819:ℝ)/8437760) = (67942400:ℝ)/67906193 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_1
  · change initialPayment 2 ≤ initialValue ((point lo 4 1024 2+point lo 4 1024 3)/2)
    have hp : initialPayment 2 = (945705612:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 2+point lo 4 1024 3)/2 = (144098233:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144098233:ℝ)/42188800) = (13588480:ℝ)/13576411 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_2
  · change initialPayment 3 ≤ initialValue ((point lo 4 1024 3+point lo 4 1024 4)/2)
    have hp : initialPayment 3 = (1324592432:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 3+point lo 4 1024 4)/2 = (144122371:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144122371:ℝ)/42188800) = (67942400:ℝ)/67857917 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_3
  · change initialPayment 4 ≤ initialValue ((point lo 4 1024 4+point lo 4 1024 5)/2)
    have hp : initialPayment 4 = (1703825037:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 4+point lo 4 1024 5)/2 = (144146509:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144146509:ℝ)/42188800) = (67942400:ℝ)/67833779 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_4
  · change initialPayment 5 ≤ initialValue ((point lo 4 1024 5+point lo 4 1024 6)/2)
    have hp : initialPayment 5 = (2083403639:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 5+point lo 4 1024 6)/2 = (144170647:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144170647:ℝ)/42188800) = (67942400:ℝ)/67809641 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_5
  · change initialPayment 6 ≤ initialValue ((point lo 4 1024 6+point lo 4 1024 7)/2)
    have hp : initialPayment 6 = (2463328448:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 6+point lo 4 1024 7)/2 = (28838957:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((28838957:ℝ)/8437760) = (67942400:ℝ)/67785503 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_6
  · change initialPayment 7 ≤ initialValue ((point lo 4 1024 7+point lo 4 1024 8)/2)
    have hp : initialPayment 7 = (2843599677:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 7+point lo 4 1024 8)/2 = (144218923:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144218923:ℝ)/42188800) = (13588480:ℝ)/13552273 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_7
  · change initialPayment 8 ≤ initialValue ((point lo 4 1024 8+point lo 4 1024 9)/2)
    have hp : initialPayment 8 = (3224217537:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 8+point lo 4 1024 9)/2 = (144243061:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144243061:ℝ)/42188800) = (67942400:ℝ)/67737227 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_8
  · change initialPayment 9 ≤ initialValue ((point lo 4 1024 9+point lo 4 1024 10)/2)
    have hp : initialPayment 9 = (3605182239:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 9+point lo 4 1024 10)/2 = (144267199:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144267199:ℝ)/42188800) = (67942400:ℝ)/67713089 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_9
  · change initialPayment 10 ≤ initialValue ((point lo 4 1024 10+point lo 4 1024 11)/2)
    have hp : initialPayment 10 = (3986493996:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 10+point lo 4 1024 11)/2 = (144291337:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144291337:ℝ)/42188800) = (67942400:ℝ)/67688951 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_10
  · change initialPayment 11 ≤ initialValue ((point lo 4 1024 11+point lo 4 1024 12)/2)
    have hp : initialPayment 11 = (4368153021:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 11+point lo 4 1024 12)/2 = (5772619:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((5772619:ℝ)/1687552) = (67942400:ℝ)/67664813 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_11
  · change initialPayment 12 ≤ initialValue ((point lo 4 1024 12+point lo 4 1024 13)/2)
    have hp : initialPayment 12 = (4750159526:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 12+point lo 4 1024 13)/2 = (144339613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144339613:ℝ)/42188800) = (2717696:ℝ)/2705627 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_12
  · change initialPayment 13 ≤ initialValue ((point lo 4 1024 13+point lo 4 1024 14)/2)
    have hp : initialPayment 13 = (5132513726:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 13+point lo 4 1024 14)/2 = (144363751:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144363751:ℝ)/42188800) = (67942400:ℝ)/67616537 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_13
  · change initialPayment 14 ≤ initialValue ((point lo 4 1024 14+point lo 4 1024 15)/2)
    have hp : initialPayment 14 = (5515215833:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 14+point lo 4 1024 15)/2 = (144387889:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144387889:ℝ)/42188800) = (67942400:ℝ)/67592399 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_14
  · change initialPayment 15 ≤ initialValue ((point lo 4 1024 15+point lo 4 1024 16)/2)
    have hp : initialPayment 15 = (5898266062:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 15+point lo 4 1024 16)/2 = (144412027:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144412027:ℝ)/42188800) = (67942400:ℝ)/67568261 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_15
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_000
