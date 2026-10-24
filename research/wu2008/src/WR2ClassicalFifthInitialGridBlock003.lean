import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints003
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_003 (j : Fin 16) : initialPayment (16*3+j.val) ≤
    initialValue ((point lo 4 1024 (16*3+j.val)+point lo 4 1024 (16*3+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 48 ≤ initialValue ((point lo 4 1024 48+point lo 4 1024 49)/2)
    have hp : initialPayment 48 = (18735640326:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 48+point lo 4 1024 49)/2 = (145208581:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145208581:ℝ)/42188800) = (67942400:ℝ)/66771707 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_48
  · change initialPayment 49 ≤ initialValue ((point lo 4 1024 49+point lo 4 1024 50)/2)
    have hp : initialPayment 49 = (19130656433:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 49+point lo 4 1024 50)/2 = (145232719:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145232719:ℝ)/42188800) = (67942400:ℝ)/66747569 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_49
  · change initialPayment 50 ≤ initialValue ((point lo 4 1024 50+point lo 4 1024 51)/2)
    have hp : initialPayment 50 = (19526028366:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 50+point lo 4 1024 51)/2 = (145256857:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145256857:ℝ)/42188800) = (67942400:ℝ)/66723431 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_50
  · change initialPayment 51 ≤ initialValue ((point lo 4 1024 51+point lo 4 1024 52)/2)
    have hp : initialPayment 51 = (19921756350:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 51+point lo 4 1024 52)/2 = (29056199:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29056199:ℝ)/8437760) = (67942400:ℝ)/66699293 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_51
  · change initialPayment 52 ≤ initialValue ((point lo 4 1024 52+point lo 4 1024 53)/2)
    have hp : initialPayment 52 = (20317840613:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 52+point lo 4 1024 53)/2 = (145305133:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145305133:ℝ)/42188800) = (13588480:ℝ)/13335031 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_52
  · change initialPayment 53 ≤ initialValue ((point lo 4 1024 53+point lo 4 1024 54)/2)
    have hp : initialPayment 53 = (20714281381:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 53+point lo 4 1024 54)/2 = (145329271:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145329271:ℝ)/42188800) = (67942400:ℝ)/66651017 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_53
  · change initialPayment 54 ≤ initialValue ((point lo 4 1024 54+point lo 4 1024 55)/2)
    have hp : initialPayment 54 = (21111078882:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 54+point lo 4 1024 55)/2 = (145353409:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145353409:ℝ)/42188800) = (67942400:ℝ)/66626879 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_54
  · change initialPayment 55 ≤ initialValue ((point lo 4 1024 55+point lo 4 1024 56)/2)
    have hp : initialPayment 55 = (21508233344:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 55+point lo 4 1024 56)/2 = (145377547:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145377547:ℝ)/42188800) = (67942400:ℝ)/66602741 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_55
  · change initialPayment 56 ≤ initialValue ((point lo 4 1024 56+point lo 4 1024 57)/2)
    have hp : initialPayment 56 = (21905744994:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 56+point lo 4 1024 57)/2 = (29080337:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((29080337:ℝ)/8437760) = (67942400:ℝ)/66578603 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_56
  · change initialPayment 57 ≤ initialValue ((point lo 4 1024 57+point lo 4 1024 58)/2)
    have hp : initialPayment 57 = (22303614061:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 57+point lo 4 1024 58)/2 = (145425823:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145425823:ℝ)/42188800) = (13588480:ℝ)/13310893 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_57
  · change initialPayment 58 ≤ initialValue ((point lo 4 1024 58+point lo 4 1024 59)/2)
    have hp : initialPayment 58 = (22701840774:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 58+point lo 4 1024 59)/2 = (145449961:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145449961:ℝ)/42188800) = (67942400:ℝ)/66530327 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_58
  · change initialPayment 59 ≤ initialValue ((point lo 4 1024 59+point lo 4 1024 60)/2)
    have hp : initialPayment 59 = (23100425361:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 59+point lo 4 1024 60)/2 = (145474099:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145474099:ℝ)/42188800) = (67942400:ℝ)/66506189 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_59
  · change initialPayment 60 ≤ initialValue ((point lo 4 1024 60+point lo 4 1024 61)/2)
    have hp : initialPayment 60 = (23499368053:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 60+point lo 4 1024 61)/2 = (145498237:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145498237:ℝ)/42188800) = (67942400:ℝ)/66482051 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_60
  · change initialPayment 61 ≤ initialValue ((point lo 4 1024 61+point lo 4 1024 62)/2)
    have hp : initialPayment 61 = (23898669080:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 61+point lo 4 1024 62)/2 = (5820895:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((5820895:ℝ)/1687552) = (67942400:ℝ)/66457913 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_61
  · change initialPayment 62 ≤ initialValue ((point lo 4 1024 62+point lo 4 1024 63)/2)
    have hp : initialPayment 62 = (24298328670:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 62+point lo 4 1024 63)/2 = (145546513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145546513:ℝ)/42188800) = (2717696:ℝ)/2657351 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_62
  · change initialPayment 63 ≤ initialValue ((point lo 4 1024 63+point lo 4 1024 64)/2)
    have hp : initialPayment 63 = (24698347056:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 63+point lo 4 1024 64)/2 = (145570651:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((145570651:ℝ)/42188800) = (67942400:ℝ)/66409637 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_63
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_003
