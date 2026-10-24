import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints050
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_050 (j : Fin 16) : initialPayment (16*50+j.val) ≤
    initialValue ((point lo 4 1024 (16*50+j.val)+point lo 4 1024 (16*50+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 800 ≤ initialValue ((point lo 4 1024 800+point lo 4 1024 801)/2)
    have hp : initialPayment 800 = (437920338049:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 800+point lo 4 1024 801)/2 = (163360357:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163360357:ℝ)/42188800) = (67942400:ℝ)/48619931 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_800
  · change initialPayment 801 ≤ initialValue ((point lo 4 1024 801+point lo 4 1024 802)/2)
    have hp : initialPayment 801 = (438679047885:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 801+point lo 4 1024 802)/2 = (32676899:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32676899:ℝ)/8437760) = (67942400:ℝ)/48595793 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_801
  · change initialPayment 802 ≤ initialValue ((point lo 4 1024 802+point lo 4 1024 803)/2)
    have hp : initialPayment 802 = (439438426627:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 802+point lo 4 1024 803)/2 = (163408633:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163408633:ℝ)/42188800) = (13588480:ℝ)/9714331 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_802
  · change initialPayment 803 ≤ initialValue ((point lo 4 1024 803+point lo 4 1024 804)/2)
    have hp : initialPayment 803 = (440198474970:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 803+point lo 4 1024 804)/2 = (163432771:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163432771:ℝ)/42188800) = (67942400:ℝ)/48547517 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_803
  · change initialPayment 804 ≤ initialValue ((point lo 4 1024 804+point lo 4 1024 805)/2)
    have hp : initialPayment 804 = (440959193612:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 804+point lo 4 1024 805)/2 = (163456909:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163456909:ℝ)/42188800) = (67942400:ℝ)/48523379 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_804
  · change initialPayment 805 ≤ initialValue ((point lo 4 1024 805+point lo 4 1024 806)/2)
    have hp : initialPayment 805 = (441720583250:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 805+point lo 4 1024 806)/2 = (163481047:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163481047:ℝ)/42188800) = (67942400:ℝ)/48499241 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_805
  · change initialPayment 806 ≤ initialValue ((point lo 4 1024 806+point lo 4 1024 807)/2)
    have hp : initialPayment 806 = (442482644584:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 806+point lo 4 1024 807)/2 = (32701037:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32701037:ℝ)/8437760) = (67942400:ℝ)/48475103 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_806
  · change initialPayment 807 ≤ initialValue ((point lo 4 1024 807+point lo 4 1024 808)/2)
    have hp : initialPayment 807 = (443245378315:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 807+point lo 4 1024 808)/2 = (163529323:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163529323:ℝ)/42188800) = (13588480:ℝ)/9690193 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_807
  · change initialPayment 808 ≤ initialValue ((point lo 4 1024 808+point lo 4 1024 809)/2)
    have hp : initialPayment 808 = (444008785144:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 808+point lo 4 1024 809)/2 = (163553461:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163553461:ℝ)/42188800) = (67942400:ℝ)/48426827 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_808
  · change initialPayment 809 ≤ initialValue ((point lo 4 1024 809+point lo 4 1024 810)/2)
    have hp : initialPayment 809 = (444772865774:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 809+point lo 4 1024 810)/2 = (163577599:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163577599:ℝ)/42188800) = (67942400:ℝ)/48402689 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_809
  · change initialPayment 810 ≤ initialValue ((point lo 4 1024 810+point lo 4 1024 811)/2)
    have hp : initialPayment 810 = (445537620908:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 810+point lo 4 1024 811)/2 = (163601737:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163601737:ℝ)/42188800) = (67942400:ℝ)/48378551 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_810
  · change initialPayment 811 ≤ initialValue ((point lo 4 1024 811+point lo 4 1024 812)/2)
    have hp : initialPayment 811 = (446303051251:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 811+point lo 4 1024 812)/2 = (6545035:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6545035:ℝ)/1687552) = (67942400:ℝ)/48354413 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_811
  · change initialPayment 812 ≤ initialValue ((point lo 4 1024 812+point lo 4 1024 813)/2)
    have hp : initialPayment 812 = (447069157510:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 812+point lo 4 1024 813)/2 = (163650013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163650013:ℝ)/42188800) = (2717696:ℝ)/1933211 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_812
  · change initialPayment 813 ≤ initialValue ((point lo 4 1024 813+point lo 4 1024 814)/2)
    have hp : initialPayment 813 = (447835940391:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 813+point lo 4 1024 814)/2 = (163674151:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163674151:ℝ)/42188800) = (67942400:ℝ)/48306137 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_813
  · change initialPayment 814 ≤ initialValue ((point lo 4 1024 814+point lo 4 1024 815)/2)
    have hp : initialPayment 814 = (448603400602:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 814+point lo 4 1024 815)/2 = (163698289:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163698289:ℝ)/42188800) = (67942400:ℝ)/48281999 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_814
  · change initialPayment 815 ≤ initialValue ((point lo 4 1024 815+point lo 4 1024 816)/2)
    have hp : initialPayment 815 = (449371538852:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 815+point lo 4 1024 816)/2 = (163722427:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((163722427:ℝ)/42188800) = (67942400:ℝ)/48257861 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_815
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_050
