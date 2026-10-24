import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints059
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_059 (j : Fin 16) : initialPayment (16*59+j.val) ≤
    initialValue ((point lo 4 1024 (16*59+j.val)+point lo 4 1024 (16*59+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 944 ≤ initialValue ((point lo 4 1024 944+point lo 4 1024 945)/2)
    have hp : initialPayment 944 = (554420675727:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 944+point lo 4 1024 945)/2 = (166836229:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166836229:ℝ)/42188800) = (67942400:ℝ)/45144059 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_944
  · change initialPayment 945 ≤ initialValue ((point lo 4 1024 945+point lo 4 1024 946)/2)
    have hp : initialPayment 945 = (555283446018:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 945+point lo 4 1024 946)/2 = (166860367:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166860367:ℝ)/42188800) = (67942400:ℝ)/45119921 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_945
  · change initialPayment 946 ≤ initialValue ((point lo 4 1024 946+point lo 4 1024 947)/2)
    have hp : initialPayment 946 = (556146997817:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 946+point lo 4 1024 947)/2 = (33376901:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33376901:ℝ)/8437760) = (67942400:ℝ)/45095783 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_946
  · change initialPayment 947 ≤ initialValue ((point lo 4 1024 947+point lo 4 1024 948)/2)
    have hp : initialPayment 947 = (557011332003:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 947+point lo 4 1024 948)/2 = (166908643:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166908643:ℝ)/42188800) = (13588480:ℝ)/9014329 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_947
  · change initialPayment 948 ≤ initialValue ((point lo 4 1024 948+point lo 4 1024 949)/2)
    have hp : initialPayment 948 = (557876449455:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 948+point lo 4 1024 949)/2 = (166932781:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166932781:ℝ)/42188800) = (67942400:ℝ)/45047507 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_948
  · change initialPayment 949 ≤ initialValue ((point lo 4 1024 949+point lo 4 1024 950)/2)
    have hp : initialPayment 949 = (558742351053:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 949+point lo 4 1024 950)/2 = (166956919:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166956919:ℝ)/42188800) = (67942400:ℝ)/45023369 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_949
  · change initialPayment 950 ≤ initialValue ((point lo 4 1024 950+point lo 4 1024 951)/2)
    have hp : initialPayment 950 = (559609037679:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 950+point lo 4 1024 951)/2 = (166981057:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166981057:ℝ)/42188800) = (67942400:ℝ)/44999231 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_950
  · change initialPayment 951 ≤ initialValue ((point lo 4 1024 951+point lo 4 1024 952)/2)
    have hp : initialPayment 951 = (560476510216:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 951+point lo 4 1024 952)/2 = (33401039:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33401039:ℝ)/8437760) = (67942400:ℝ)/44975093 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_951
  · change initialPayment 952 ≤ initialValue ((point lo 4 1024 952+point lo 4 1024 953)/2)
    have hp : initialPayment 952 = (561344769551:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 952+point lo 4 1024 953)/2 = (167029333:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167029333:ℝ)/42188800) = (13588480:ℝ)/8990191 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_952
  · change initialPayment 953 ≤ initialValue ((point lo 4 1024 953+point lo 4 1024 954)/2)
    have hp : initialPayment 953 = (562213816568:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 953+point lo 4 1024 954)/2 = (167053471:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167053471:ℝ)/42188800) = (67942400:ℝ)/44926817 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_953
  · change initialPayment 954 ≤ initialValue ((point lo 4 1024 954+point lo 4 1024 955)/2)
    have hp : initialPayment 954 = (563083652157:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 954+point lo 4 1024 955)/2 = (167077609:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167077609:ℝ)/42188800) = (67942400:ℝ)/44902679 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_954
  · change initialPayment 955 ≤ initialValue ((point lo 4 1024 955+point lo 4 1024 956)/2)
    have hp : initialPayment 955 = (563954277205:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 955+point lo 4 1024 956)/2 = (167101747:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167101747:ℝ)/42188800) = (67942400:ℝ)/44878541 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_955
  · change initialPayment 956 ≤ initialValue ((point lo 4 1024 956+point lo 4 1024 957)/2)
    have hp : initialPayment 956 = (564825692606:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 956+point lo 4 1024 957)/2 = (33425177:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33425177:ℝ)/8437760) = (67942400:ℝ)/44854403 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_956
  · change initialPayment 957 ≤ initialValue ((point lo 4 1024 957+point lo 4 1024 958)/2)
    have hp : initialPayment 957 = (565697899249:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 957+point lo 4 1024 958)/2 = (167150023:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167150023:ℝ)/42188800) = (13588480:ℝ)/8966053 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_957
  · change initialPayment 958 ≤ initialValue ((point lo 4 1024 958+point lo 4 1024 959)/2)
    have hp : initialPayment 958 = (566570898031:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 958+point lo 4 1024 959)/2 = (167174161:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167174161:ℝ)/42188800) = (67942400:ℝ)/44806127 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_958
  · change initialPayment 959 ≤ initialValue ((point lo 4 1024 959+point lo 4 1024 960)/2)
    have hp : initialPayment 959 = (567444689844:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 959+point lo 4 1024 960)/2 = (167198299:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((167198299:ℝ)/42188800) = (67942400:ℝ)/44781989 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_959
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_059
