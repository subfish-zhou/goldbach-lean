import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints001
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_001 (j : Fin 16) : initialPayment (16*1+j.val) ≤
    initialValue ((point lo 4 1024 (16*1+j.val)+point lo 4 1024 (16*1+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 16 ≤ initialValue ((point lo 4 1024 16+point lo 4 1024 17)/2)
    have hp : initialPayment 16 = (6281664626:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 16+point lo 4 1024 17)/2 = (28887233:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((28887233:ℝ)/8437760) = (67942400:ℝ)/67544123 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_16
  · change initialPayment 17 ≤ initialValue ((point lo 4 1024 17+point lo 4 1024 18)/2)
    have hp : initialPayment 17 = (6665411742:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 17+point lo 4 1024 18)/2 = (144460303:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144460303:ℝ)/42188800) = (13588480:ℝ)/13503997 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_17
  · change initialPayment 18 ≤ initialValue ((point lo 4 1024 18+point lo 4 1024 19)/2)
    have hp : initialPayment 18 = (7049507623:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 18+point lo 4 1024 19)/2 = (144484441:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144484441:ℝ)/42188800) = (67942400:ℝ)/67495847 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_18
  · change initialPayment 19 ≤ initialValue ((point lo 4 1024 19+point lo 4 1024 20)/2)
    have hp : initialPayment 19 = (7433952485:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 19+point lo 4 1024 20)/2 = (144508579:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144508579:ℝ)/42188800) = (67942400:ℝ)/67471709 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_19
  · change initialPayment 20 ≤ initialValue ((point lo 4 1024 20+point lo 4 1024 21)/2)
    have hp : initialPayment 20 = (7818746543:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 20+point lo 4 1024 21)/2 = (144532717:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144532717:ℝ)/42188800) = (67942400:ℝ)/67447571 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_20
  · change initialPayment 21 ≤ initialValue ((point lo 4 1024 21+point lo 4 1024 22)/2)
    have hp : initialPayment 21 = (8203890014:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 21+point lo 4 1024 22)/2 = (28911371:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((28911371:ℝ)/8437760) = (67942400:ℝ)/67423433 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_21
  · change initialPayment 22 ≤ initialValue ((point lo 4 1024 22+point lo 4 1024 23)/2)
    have hp : initialPayment 22 = (8589383114:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 22+point lo 4 1024 23)/2 = (144580993:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144580993:ℝ)/42188800) = (13588480:ℝ)/13479859 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_22
  · change initialPayment 23 ≤ initialValue ((point lo 4 1024 23+point lo 4 1024 24)/2)
    have hp : initialPayment 23 = (8975226060:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 23+point lo 4 1024 24)/2 = (144605131:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144605131:ℝ)/42188800) = (67942400:ℝ)/67375157 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_23
  · change initialPayment 24 ≤ initialValue ((point lo 4 1024 24+point lo 4 1024 25)/2)
    have hp : initialPayment 24 = (9361419069:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 24+point lo 4 1024 25)/2 = (144629269:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144629269:ℝ)/42188800) = (67942400:ℝ)/67351019 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_24
  · change initialPayment 25 ≤ initialValue ((point lo 4 1024 25+point lo 4 1024 26)/2)
    have hp : initialPayment 25 = (9747962357:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 25+point lo 4 1024 26)/2 = (144653407:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144653407:ℝ)/42188800) = (67942400:ℝ)/67326881 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_25
  · change initialPayment 26 ≤ initialValue ((point lo 4 1024 26+point lo 4 1024 27)/2)
    have hp : initialPayment 26 = (10134856144:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 26+point lo 4 1024 27)/2 = (28935509:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((28935509:ℝ)/8437760) = (67942400:ℝ)/67302743 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_26
  · change initialPayment 27 ≤ initialValue ((point lo 4 1024 27+point lo 4 1024 28)/2)
    have hp : initialPayment 27 = (10522100646:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 27+point lo 4 1024 28)/2 = (144701683:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144701683:ℝ)/42188800) = (13588480:ℝ)/13455721 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_27
  · change initialPayment 28 ≤ initialValue ((point lo 4 1024 28+point lo 4 1024 29)/2)
    have hp : initialPayment 28 = (10909696082:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 28+point lo 4 1024 29)/2 = (144725821:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144725821:ℝ)/42188800) = (67942400:ℝ)/67254467 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_28
  · change initialPayment 29 ≤ initialValue ((point lo 4 1024 29+point lo 4 1024 30)/2)
    have hp : initialPayment 29 = (11297642671:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 29+point lo 4 1024 30)/2 = (144749959:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144749959:ℝ)/42188800) = (67942400:ℝ)/67230329 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_29
  · change initialPayment 30 ≤ initialValue ((point lo 4 1024 30+point lo 4 1024 31)/2)
    have hp : initialPayment 30 = (11685940633:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 30+point lo 4 1024 31)/2 = (144774097:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144774097:ℝ)/42188800) = (67942400:ℝ)/67206191 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_30
  · change initialPayment 31 ≤ initialValue ((point lo 4 1024 31+point lo 4 1024 32)/2)
    have hp : initialPayment 31 = (12074590185:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 31+point lo 4 1024 32)/2 = (28959647:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((28959647:ℝ)/8437760) = (67942400:ℝ)/67182053 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_31
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_001
