import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints002
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_002 (j : Fin 16) : initialPayment (16*2+j.val) ≤
    initialValue ((point lo 4 1024 (16*2+j.val)+point lo 4 1024 (16*2+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 32 ≤ initialValue ((point lo 4 1024 32+point lo 4 1024 33)/2)
    have hp : initialPayment 32 = (12463591549:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 32+point lo 4 1024 33)/2 = (144822373:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144822373:ℝ)/42188800) = (13588480:ℝ)/13431583 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_32
  · change initialPayment 33 ≤ initialValue ((point lo 4 1024 33+point lo 4 1024 34)/2)
    have hp : initialPayment 33 = (12852944944:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 33+point lo 4 1024 34)/2 = (144846511:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144846511:ℝ)/42188800) = (67942400:ℝ)/67133777 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_33
  · change initialPayment 34 ≤ initialValue ((point lo 4 1024 34+point lo 4 1024 35)/2)
    have hp : initialPayment 34 = (13242650590:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 34+point lo 4 1024 35)/2 = (144870649:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144870649:ℝ)/42188800) = (67942400:ℝ)/67109639 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_34
  · change initialPayment 35 ≤ initialValue ((point lo 4 1024 35+point lo 4 1024 36)/2)
    have hp : initialPayment 35 = (13632708709:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 35+point lo 4 1024 36)/2 = (144894787:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144894787:ℝ)/42188800) = (67942400:ℝ)/67085501 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_35
  · change initialPayment 36 ≤ initialValue ((point lo 4 1024 36+point lo 4 1024 37)/2)
    have hp : initialPayment 36 = (14023119522:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 36+point lo 4 1024 37)/2 = (5796757:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((5796757:ℝ)/1687552) = (67942400:ℝ)/67061363 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_36
  · change initialPayment 37 ≤ initialValue ((point lo 4 1024 37+point lo 4 1024 38)/2)
    have hp : initialPayment 37 = (14413883250:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 37+point lo 4 1024 38)/2 = (144943063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144943063:ℝ)/42188800) = (2717696:ℝ)/2681489 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_37
  · change initialPayment 38 ≤ initialValue ((point lo 4 1024 38+point lo 4 1024 39)/2)
    have hp : initialPayment 38 = (14805000114:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 38+point lo 4 1024 39)/2 = (144967201:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144967201:ℝ)/42188800) = (67942400:ℝ)/67013087 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_38
  · change initialPayment 39 ≤ initialValue ((point lo 4 1024 39+point lo 4 1024 40)/2)
    have hp : initialPayment 39 = (15196470337:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 39+point lo 4 1024 40)/2 = (144991339:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((144991339:ℝ)/42188800) = (67942400:ℝ)/66988949 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_39
  · change initialPayment 40 ≤ initialValue ((point lo 4 1024 40+point lo 4 1024 41)/2)
    have hp : initialPayment 40 = (15588294142:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 40+point lo 4 1024 41)/2 = (145015477:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145015477:ℝ)/42188800) = (67942400:ℝ)/66964811 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_40
  · change initialPayment 41 ≤ initialValue ((point lo 4 1024 41+point lo 4 1024 42)/2)
    have hp : initialPayment 41 = (15980471751:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 41+point lo 4 1024 42)/2 = (29007923:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29007923:ℝ)/8437760) = (67942400:ℝ)/66940673 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_41
  · change initialPayment 42 ≤ initialValue ((point lo 4 1024 42+point lo 4 1024 43)/2)
    have hp : initialPayment 42 = (16373003388:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 42+point lo 4 1024 43)/2 = (145063753:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145063753:ℝ)/42188800) = (13588480:ℝ)/13383307 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_42
  · change initialPayment 43 ≤ initialValue ((point lo 4 1024 43+point lo 4 1024 44)/2)
    have hp : initialPayment 43 = (16765889275:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 43+point lo 4 1024 44)/2 = (145087891:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145087891:ℝ)/42188800) = (67942400:ℝ)/66892397 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_43
  · change initialPayment 44 ≤ initialValue ((point lo 4 1024 44+point lo 4 1024 45)/2)
    have hp : initialPayment 44 = (17159129638:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 44+point lo 4 1024 45)/2 = (145112029:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145112029:ℝ)/42188800) = (67942400:ℝ)/66868259 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_44
  · change initialPayment 45 ≤ initialValue ((point lo 4 1024 45+point lo 4 1024 46)/2)
    have hp : initialPayment 45 = (17552724699:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 45+point lo 4 1024 46)/2 = (1409089:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((1409089:ℝ)/409600) = (67942400:ℝ)/66844121 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_45
  · change initialPayment 46 ≤ initialValue ((point lo 4 1024 46+point lo 4 1024 47)/2)
    have hp : initialPayment 46 = (17946674684:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 46+point lo 4 1024 47)/2 = (29032061:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29032061:ℝ)/8437760) = (67942400:ℝ)/66819983 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_46
  · change initialPayment 47 ≤ initialValue ((point lo 4 1024 47+point lo 4 1024 48)/2)
    have hp : initialPayment 47 = (18340979818:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 47+point lo 4 1024 48)/2 = (145184443:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145184443:ℝ)/42188800) = (13588480:ℝ)/13359169 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_47
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_002
