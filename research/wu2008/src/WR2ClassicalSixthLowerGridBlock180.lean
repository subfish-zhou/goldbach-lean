import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints180
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_180 (j : Fin 16) : lowerPayment (16*180+j.val) ≤
    lowerValue ((point 2 split 4096 (16*180+j.val)+point 2 split 4096 (16*180+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2880 ≤ lowerValue ((point 2 split 4096 2880+point 2 split 4096 2881)/2)
    have hp : lowerPayment 2880 = (310690962670:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2880+point 2 split 4096 2881)/2 = (505334091:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505334091:ℝ)/168755200)/ClassicalSixthBranch.v ((505334091:ℝ)/168755200) = (591313138747:ℝ)/282291738264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2880
  · change lowerPayment 2881 ≤ lowerValue ((point 2 split 4096 2881+point 2 split 4096 2882)/2)
    have hp : lowerPayment 2881 = (310779027419:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2881+point 2 split 4096 2882)/2 = (505392353:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505392353:ℝ)/168755200)/ClassicalSixthBranch.v ((505392353:ℝ)/168755200) = (591235825073:ℝ)/282243730376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2881
  · change lowerPayment 2882 ≤ lowerValue ((point 2 split 4096 2882+point 2 split 4096 2883)/2)
    have hp : lowerPayment 2882 = (310867095143:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2882+point 2 split 4096 2883)/2 = (101090123:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101090123:ℝ)/33751040)/ClassicalSixthBranch.v ((101090123:ℝ)/33751040) = (591158511399:ℝ)/282195722488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2882
  · change lowerPayment 2883 ≤ lowerValue ((point 2 split 4096 2883+point 2 split 4096 2884)/2)
    have hp : lowerPayment 2883 = (310955165854:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2883+point 2 split 4096 2884)/2 = (505508877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505508877:ℝ)/168755200)/ClassicalSixthBranch.v ((505508877:ℝ)/168755200) = (23643247909:ℝ)/11285908584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2883
  · change lowerPayment 2884 ≤ lowerValue ((point 2 split 4096 2884+point 2 split 4096 2885)/2)
    have hp : lowerPayment 2884 = (311043239567:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2884+point 2 split 4096 2885)/2 = (505567139:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505567139:ℝ)/168755200)/ClassicalSixthBranch.v ((505567139:ℝ)/168755200) = (591003884051:ℝ)/282099706712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2884
  · change lowerPayment 2885 ≤ lowerValue ((point 2 split 4096 2885+point 2 split 4096 2886)/2)
    have hp : lowerPayment 2885 = (311131316296:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2885+point 2 split 4096 2886)/2 = (505625401:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505625401:ℝ)/168755200)/ClassicalSixthBranch.v ((505625401:ℝ)/168755200) = (590926570377:ℝ)/282051698824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2885
  · change lowerPayment 2886 ≤ lowerValue ((point 2 split 4096 2886+point 2 split 4096 2887)/2)
    have hp : lowerPayment 2886 = (311219396056:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2886+point 2 split 4096 2887)/2 = (505683663:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505683663:ℝ)/168755200)/ClassicalSixthBranch.v ((505683663:ℝ)/168755200) = (590849256703:ℝ)/282003690936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2886
  · change lowerPayment 2887 ≤ lowerValue ((point 2 split 4096 2887+point 2 split 4096 2888)/2)
    have hp : lowerPayment 2887 = (311307478860:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2887+point 2 split 4096 2888)/2 = (20229677:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20229677:ℝ)/6750208)/ClassicalSixthBranch.v ((20229677:ℝ)/6750208) = (590771943029:ℝ)/281955683048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2887
  · change lowerPayment 2888 ≤ lowerValue ((point 2 split 4096 2888+point 2 split 4096 2889)/2)
    have hp : lowerPayment 2888 = (311395564722:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2888+point 2 split 4096 2889)/2 = (505800187:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505800187:ℝ)/168755200)/ClassicalSixthBranch.v ((505800187:ℝ)/168755200) = (118138925871:ℝ)/56381535032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2888
  · change lowerPayment 2889 ≤ lowerValue ((point 2 split 4096 2889+point 2 split 4096 2890)/2)
    have hp : lowerPayment 2889 = (311483653657:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2889+point 2 split 4096 2890)/2 = (505858449:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505858449:ℝ)/168755200)/ClassicalSixthBranch.v ((505858449:ℝ)/168755200) = (590617315681:ℝ)/281859667272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2889
  · change lowerPayment 2890 ≤ lowerValue ((point 2 split 4096 2890+point 2 split 4096 2891)/2)
    have hp : lowerPayment 2890 = (311571745679:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2890+point 2 split 4096 2891)/2 = (505916711:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505916711:ℝ)/168755200)/ClassicalSixthBranch.v ((505916711:ℝ)/168755200) = (590540002007:ℝ)/281811659384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2890
  · change lowerPayment 2891 ≤ lowerValue ((point 2 split 4096 2891+point 2 split 4096 2892)/2)
    have hp : lowerPayment 2891 = (311659840801:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2891+point 2 split 4096 2892)/2 = (505974973:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((505974973:ℝ)/168755200)/ClassicalSixthBranch.v ((505974973:ℝ)/168755200) = (590462688333:ℝ)/281763651496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2891
  · change lowerPayment 2892 ≤ lowerValue ((point 2 split 4096 2892+point 2 split 4096 2893)/2)
    have hp : lowerPayment 2892 = (311747939039:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2892+point 2 split 4096 2893)/2 = (101206647:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101206647:ℝ)/33751040)/ClassicalSixthBranch.v ((101206647:ℝ)/33751040) = (590385374659:ℝ)/281715643608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2892
  · change lowerPayment 2893 ≤ lowerValue ((point 2 split 4096 2893+point 2 split 4096 2894)/2)
    have hp : lowerPayment 2893 = (311836040405:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2893+point 2 split 4096 2894)/2 = (506091497:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506091497:ℝ)/168755200)/ClassicalSixthBranch.v ((506091497:ℝ)/168755200) = (118061612197:ℝ)/56333527144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2893
  · change lowerPayment 2894 ≤ lowerValue ((point 2 split 4096 2894+point 2 split 4096 2895)/2)
    have hp : lowerPayment 2894 = (311924144914:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2894+point 2 split 4096 2895)/2 = (506149759:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506149759:ℝ)/168755200)/ClassicalSixthBranch.v ((506149759:ℝ)/168755200) = (590230747311:ℝ)/281619627832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2894
  · change lowerPayment 2895 ≤ lowerValue ((point 2 split 4096 2895+point 2 split 4096 2896)/2)
    have hp : lowerPayment 2895 = (312012252581:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2895+point 2 split 4096 2896)/2 = (506208021:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((506208021:ℝ)/168755200)/ClassicalSixthBranch.v ((506208021:ℝ)/168755200) = (590153433637:ℝ)/281571619944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2895
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_180
