import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints004
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_004 (j : Fin 16) : initialPayment (16*4+j.val) ≤
    initialValue ((point lo 4 1024 (16*4+j.val)+point lo 4 1024 (16*4+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 64 ≤ initialValue ((point lo 4 1024 64+point lo 4 1024 65)/2)
    have hp : initialPayment 64 = (25098724467:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 64+point lo 4 1024 65)/2 = (145594789:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145594789:ℝ)/42188800) = (67942400:ℝ)/66385499 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_64
  · change initialPayment 65 ≤ initialValue ((point lo 4 1024 65+point lo 4 1024 66)/2)
    have hp : initialPayment 65 = (25499461136:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 65+point lo 4 1024 66)/2 = (145618927:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145618927:ℝ)/42188800) = (67942400:ℝ)/66361361 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_65
  · change initialPayment 66 ≤ initialValue ((point lo 4 1024 66+point lo 4 1024 67)/2)
    have hp : initialPayment 66 = (25900557293:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 66+point lo 4 1024 67)/2 = (29128613:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29128613:ℝ)/8437760) = (67942400:ℝ)/66337223 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_66
  · change initialPayment 67 ≤ initialValue ((point lo 4 1024 67+point lo 4 1024 68)/2)
    have hp : initialPayment 67 = (26302013170:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 67+point lo 4 1024 68)/2 = (145667203:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145667203:ℝ)/42188800) = (13588480:ℝ)/13262617 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_67
  · change initialPayment 68 ≤ initialValue ((point lo 4 1024 68+point lo 4 1024 69)/2)
    have hp : initialPayment 68 = (26703829001:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 68+point lo 4 1024 69)/2 = (145691341:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145691341:ℝ)/42188800) = (67942400:ℝ)/66288947 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_68
  · change initialPayment 69 ≤ initialValue ((point lo 4 1024 69+point lo 4 1024 70)/2)
    have hp : initialPayment 69 = (27106005017:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 69+point lo 4 1024 70)/2 = (145715479:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145715479:ℝ)/42188800) = (67942400:ℝ)/66264809 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_69
  · change initialPayment 70 ≤ initialValue ((point lo 4 1024 70+point lo 4 1024 71)/2)
    have hp : initialPayment 70 = (27508541451:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 70+point lo 4 1024 71)/2 = (145739617:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145739617:ℝ)/42188800) = (67942400:ℝ)/66240671 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_70
  · change initialPayment 71 ≤ initialValue ((point lo 4 1024 71+point lo 4 1024 72)/2)
    have hp : initialPayment 71 = (27911438538:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 71+point lo 4 1024 72)/2 = (29152751:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29152751:ℝ)/8437760) = (67942400:ℝ)/66216533 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_71
  · change initialPayment 72 ≤ initialValue ((point lo 4 1024 72+point lo 4 1024 73)/2)
    have hp : initialPayment 72 = (28314696510:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 72+point lo 4 1024 73)/2 = (145787893:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145787893:ℝ)/42188800) = (13588480:ℝ)/13238479 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_72
  · change initialPayment 73 ≤ initialValue ((point lo 4 1024 73+point lo 4 1024 74)/2)
    have hp : initialPayment 73 = (28718315602:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 73+point lo 4 1024 74)/2 = (145812031:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145812031:ℝ)/42188800) = (67942400:ℝ)/66168257 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_73
  · change initialPayment 74 ≤ initialValue ((point lo 4 1024 74+point lo 4 1024 75)/2)
    have hp : initialPayment 74 = (29122296048:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 74+point lo 4 1024 75)/2 = (145836169:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145836169:ℝ)/42188800) = (67942400:ℝ)/66144119 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_74
  · change initialPayment 75 ≤ initialValue ((point lo 4 1024 75+point lo 4 1024 76)/2)
    have hp : initialPayment 75 = (29526638084:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 75+point lo 4 1024 76)/2 = (145860307:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145860307:ℝ)/42188800) = (67942400:ℝ)/66119981 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_75
  · change initialPayment 76 ≤ initialValue ((point lo 4 1024 76+point lo 4 1024 77)/2)
    have hp : initialPayment 76 = (29931341943:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 76+point lo 4 1024 77)/2 = (29176889:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29176889:ℝ)/8437760) = (67942400:ℝ)/66095843 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_76
  · change initialPayment 77 ≤ initialValue ((point lo 4 1024 77+point lo 4 1024 78)/2)
    have hp : initialPayment 77 = (30336407863:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 77+point lo 4 1024 78)/2 = (145908583:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145908583:ℝ)/42188800) = (13588480:ℝ)/13214341 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_77
  · change initialPayment 78 ≤ initialValue ((point lo 4 1024 78+point lo 4 1024 79)/2)
    have hp : initialPayment 78 = (30741836078:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 78+point lo 4 1024 79)/2 = (145932721:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145932721:ℝ)/42188800) = (67942400:ℝ)/66047567 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_78
  · change initialPayment 79 ≤ initialValue ((point lo 4 1024 79+point lo 4 1024 80)/2)
    have hp : initialPayment 79 = (31147626825:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 79+point lo 4 1024 80)/2 = (145956859:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145956859:ℝ)/42188800) = (67942400:ℝ)/66023429 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_79
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_004
