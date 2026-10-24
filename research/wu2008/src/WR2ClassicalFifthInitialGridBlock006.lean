import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints006
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_006 (j : Fin 16) : initialPayment (16*6+j.val) ≤
    initialValue ((point lo 4 1024 (16*6+j.val)+point lo 4 1024 (16*6+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 96 ≤ initialValue ((point lo 4 1024 96+point lo 4 1024 97)/2)
    have hp : initialPayment 96 = (38101767595:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 96+point lo 4 1024 97)/2 = (29273441:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29273441:ℝ)/8437760) = (67942400:ℝ)/65613083 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_96
  · change initialPayment 97 ≤ initialValue ((point lo 4 1024 97+point lo 4 1024 98)/2)
    have hp : initialPayment 97 = (38514124730:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 97+point lo 4 1024 98)/2 = (146391343:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146391343:ℝ)/42188800) = (13588480:ℝ)/13117789 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_97
  · change initialPayment 98 ≤ initialValue ((point lo 4 1024 98+point lo 4 1024 99)/2)
    have hp : initialPayment 98 = (38926848955:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 98+point lo 4 1024 99)/2 = (146415481:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146415481:ℝ)/42188800) = (67942400:ℝ)/65564807 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_98
  · change initialPayment 99 ≤ initialValue ((point lo 4 1024 99+point lo 4 1024 100)/2)
    have hp : initialPayment 99 = (39339940513:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 99+point lo 4 1024 100)/2 = (146439619:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146439619:ℝ)/42188800) = (67942400:ℝ)/65540669 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_99
  · change initialPayment 100 ≤ initialValue ((point lo 4 1024 100+point lo 4 1024 101)/2)
    have hp : initialPayment 100 = (39753399649:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 100+point lo 4 1024 101)/2 = (146463757:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146463757:ℝ)/42188800) = (67942400:ℝ)/65516531 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_100
  · change initialPayment 101 ≤ initialValue ((point lo 4 1024 101+point lo 4 1024 102)/2)
    have hp : initialPayment 101 = (40167226606:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 101+point lo 4 1024 102)/2 = (29297579:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29297579:ℝ)/8437760) = (67942400:ℝ)/65492393 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_101
  · change initialPayment 102 ≤ initialValue ((point lo 4 1024 102+point lo 4 1024 103)/2)
    have hp : initialPayment 102 = (40581421630:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 102+point lo 4 1024 103)/2 = (146512033:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146512033:ℝ)/42188800) = (13588480:ℝ)/13093651 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_102
  · change initialPayment 103 ≤ initialValue ((point lo 4 1024 103+point lo 4 1024 104)/2)
    have hp : initialPayment 103 = (40995984965:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 103+point lo 4 1024 104)/2 = (146536171:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146536171:ℝ)/42188800) = (67942400:ℝ)/65444117 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_103
  · change initialPayment 104 ≤ initialValue ((point lo 4 1024 104+point lo 4 1024 105)/2)
    have hp : initialPayment 104 = (41410916857:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 104+point lo 4 1024 105)/2 = (146560309:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146560309:ℝ)/42188800) = (67942400:ℝ)/65419979 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_104
  · change initialPayment 105 ≤ initialValue ((point lo 4 1024 105+point lo 4 1024 106)/2)
    have hp : initialPayment 105 = (41826217552:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 105+point lo 4 1024 106)/2 = (146584447:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146584447:ℝ)/42188800) = (67942400:ℝ)/65395841 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_105
  · change initialPayment 106 ≤ initialValue ((point lo 4 1024 106+point lo 4 1024 107)/2)
    have hp : initialPayment 106 = (42241887295:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 106+point lo 4 1024 107)/2 = (29321717:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29321717:ℝ)/8437760) = (67942400:ℝ)/65371703 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_106
  · change initialPayment 107 ≤ initialValue ((point lo 4 1024 107+point lo 4 1024 108)/2)
    have hp : initialPayment 107 = (42657926333:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 107+point lo 4 1024 108)/2 = (146632723:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146632723:ℝ)/42188800) = (13588480:ℝ)/13069513 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_107
  · change initialPayment 108 ≤ initialValue ((point lo 4 1024 108+point lo 4 1024 109)/2)
    have hp : initialPayment 108 = (43074334914:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 108+point lo 4 1024 109)/2 = (146656861:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146656861:ℝ)/42188800) = (67942400:ℝ)/65323427 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_108
  · change initialPayment 109 ≤ initialValue ((point lo 4 1024 109+point lo 4 1024 110)/2)
    have hp : initialPayment 109 = (43491113284:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 109+point lo 4 1024 110)/2 = (146680999:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146680999:ℝ)/42188800) = (67942400:ℝ)/65299289 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_109
  · change initialPayment 110 ≤ initialValue ((point lo 4 1024 110+point lo 4 1024 111)/2)
    have hp : initialPayment 110 = (43908261691:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 110+point lo 4 1024 111)/2 = (146705137:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((146705137:ℝ)/42188800) = (67942400:ℝ)/65275151 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_110
  · change initialPayment 111 ≤ initialValue ((point lo 4 1024 111+point lo 4 1024 112)/2)
    have hp : initialPayment 111 = (44325780383:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 111+point lo 4 1024 112)/2 = (5869171:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((5869171:ℝ)/1687552) = (67942400:ℝ)/65251013 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_111
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_006
