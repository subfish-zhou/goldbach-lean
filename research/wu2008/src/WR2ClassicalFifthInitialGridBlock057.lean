import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints057
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_057 (j : Fin 16) : initialPayment (16*57+j.val) ≤
    initialValue ((point lo 4 1024 (16*57+j.val)+point lo 4 1024 (16*57+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 912 ≤ initialValue ((point lo 4 1024 912+point lo 4 1024 913)/2)
    have hp : initialPayment 912 = (527219485842:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 912+point lo 4 1024 913)/2 = (166063813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166063813:ℝ)/42188800) = (2717696:ℝ)/1836659 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_912
  · change initialPayment 913 ≤ initialValue ((point lo 4 1024 913+point lo 4 1024 914)/2)
    have hp : initialPayment 913 = (528057702739:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 913+point lo 4 1024 914)/2 = (166087951:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166087951:ℝ)/42188800) = (67942400:ℝ)/45892337 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_913
  · change initialPayment 914 ≤ initialValue ((point lo 4 1024 914+point lo 4 1024 915)/2)
    have hp : initialPayment 914 = (528896673808:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 914+point lo 4 1024 915)/2 = (166112089:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166112089:ℝ)/42188800) = (67942400:ℝ)/45868199 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_914
  · change initialPayment 915 ≤ initialValue ((point lo 4 1024 915+point lo 4 1024 916)/2)
    have hp : initialPayment 915 = (529736399881:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 915+point lo 4 1024 916)/2 = (166136227:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166136227:ℝ)/42188800) = (67942400:ℝ)/45844061 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_915
  · change initialPayment 916 ≤ initialValue ((point lo 4 1024 916+point lo 4 1024 917)/2)
    have hp : initialPayment 916 = (530576881793:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 916+point lo 4 1024 917)/2 = (33232073:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33232073:ℝ)/8437760) = (67942400:ℝ)/45819923 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_916
  · change initialPayment 917 ≤ initialValue ((point lo 4 1024 917+point lo 4 1024 918)/2)
    have hp : initialPayment 917 = (531418120379:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 917+point lo 4 1024 918)/2 = (166184503:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166184503:ℝ)/42188800) = (13588480:ℝ)/9159157 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_917
  · change initialPayment 918 ≤ initialValue ((point lo 4 1024 918+point lo 4 1024 919)/2)
    have hp : initialPayment 918 = (532260116476:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 918+point lo 4 1024 919)/2 = (166208641:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166208641:ℝ)/42188800) = (67942400:ℝ)/45771647 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_918
  · change initialPayment 919 ≤ initialValue ((point lo 4 1024 919+point lo 4 1024 920)/2)
    have hp : initialPayment 919 = (533102870923:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 919+point lo 4 1024 920)/2 = (166232779:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166232779:ℝ)/42188800) = (67942400:ℝ)/45747509 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_919
  · change initialPayment 920 ≤ initialValue ((point lo 4 1024 920+point lo 4 1024 921)/2)
    have hp : initialPayment 920 = (533946384558:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 920+point lo 4 1024 921)/2 = (166256917:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166256917:ℝ)/42188800) = (67942400:ℝ)/45723371 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_920
  · change initialPayment 921 ≤ initialValue ((point lo 4 1024 921+point lo 4 1024 922)/2)
    have hp : initialPayment 921 = (534790658223:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 921+point lo 4 1024 922)/2 = (33256211:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33256211:ℝ)/8437760) = (67942400:ℝ)/45699233 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_921
  · change initialPayment 922 ≤ initialValue ((point lo 4 1024 922+point lo 4 1024 923)/2)
    have hp : initialPayment 922 = (535635692760:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 922+point lo 4 1024 923)/2 = (166305193:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166305193:ℝ)/42188800) = (13588480:ℝ)/9135019 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_922
  · change initialPayment 923 ≤ initialValue ((point lo 4 1024 923+point lo 4 1024 924)/2)
    have hp : initialPayment 923 = (536481489014:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 923+point lo 4 1024 924)/2 = (166329331:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166329331:ℝ)/42188800) = (67942400:ℝ)/45650957 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_923
  · change initialPayment 924 ≤ initialValue ((point lo 4 1024 924+point lo 4 1024 925)/2)
    have hp : initialPayment 924 = (537328047828:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 924+point lo 4 1024 925)/2 = (166353469:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166353469:ℝ)/42188800) = (67942400:ℝ)/45626819 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_924
  · change initialPayment 925 ≤ initialValue ((point lo 4 1024 925+point lo 4 1024 926)/2)
    have hp : initialPayment 925 = (538175370049:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 925+point lo 4 1024 926)/2 = (166377607:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166377607:ℝ)/42188800) = (67942400:ℝ)/45602681 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_925
  · change initialPayment 926 ≤ initialValue ((point lo 4 1024 926+point lo 4 1024 927)/2)
    have hp : initialPayment 926 = (539023456526:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 926+point lo 4 1024 927)/2 = (33280349:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((33280349:ℝ)/8437760) = (67942400:ℝ)/45578543 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_926
  · change initialPayment 927 ≤ initialValue ((point lo 4 1024 927+point lo 4 1024 928)/2)
    have hp : initialPayment 927 = (539872308107:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 927+point lo 4 1024 928)/2 = (166425883:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((166425883:ℝ)/42188800) = (13588480:ℝ)/9110881 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_927
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_057
