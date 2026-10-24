import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints055
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_055 (j : Fin 16) : lowerPayment (16*55+j.val) ≤
    lowerValue ((point 2 split 4096 (16*55+j.val)+point 2 split 4096 (16*55+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 880 ≤ lowerValue ((point 2 split 4096 880+point 2 split 4096 881)/2)
    have hp : lowerPayment 880 = (119825204000:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 880+point 2 split 4096 881)/2 = (388810091:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((388810091:ℝ)/168755200)/ClassicalSixthBranch.v ((388810091:ℝ)/168755200) = (745940486747:ℝ)/378307514264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_880
  · change lowerPayment 881 ≤ lowerValue ((point 2 split 4096 881+point 2 split 4096 882)/2)
    have hp : lowerPayment 881 = (119940411151:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 881+point 2 split 4096 882)/2 = (388868353:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((388868353:ℝ)/168755200)/ClassicalSixthBranch.v ((388868353:ℝ)/168755200) = (745863173073:ℝ)/378259506376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_881
  · change lowerPayment 882 ≤ lowerValue ((point 2 split 4096 882+point 2 split 4096 883)/2)
    have hp : lowerPayment 882 = (120055582524:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 882+point 2 split 4096 883)/2 = (77785323:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77785323:ℝ)/33751040)/ClassicalSixthBranch.v ((77785323:ℝ)/33751040) = (745785859399:ℝ)/378211498488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_882
  · change lowerPayment 883 ≤ lowerValue ((point 2 split 4096 883+point 2 split 4096 884)/2)
    have hp : lowerPayment 883 = (120170718152:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 883+point 2 split 4096 884)/2 = (388984877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((388984877:ℝ)/168755200)/ClassicalSixthBranch.v ((388984877:ℝ)/168755200) = (29828341829:ℝ)/15126539624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_883
  · change lowerPayment 884 ≤ lowerValue ((point 2 split 4096 884+point 2 split 4096 885)/2)
    have hp : lowerPayment 884 = (120285818067:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 884+point 2 split 4096 885)/2 = (389043139:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389043139:ℝ)/168755200)/ClassicalSixthBranch.v ((389043139:ℝ)/168755200) = (745631232051:ℝ)/378115482712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_884
  · change lowerPayment 885 ≤ lowerValue ((point 2 split 4096 885+point 2 split 4096 886)/2)
    have hp : lowerPayment 885 = (120400882301:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 885+point 2 split 4096 886)/2 = (389101401:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389101401:ℝ)/168755200)/ClassicalSixthBranch.v ((389101401:ℝ)/168755200) = (745553918377:ℝ)/378067474824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_885
  · change lowerPayment 886 ≤ lowerValue ((point 2 split 4096 886+point 2 split 4096 887)/2)
    have hp : lowerPayment 886 = (120515910887:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 886+point 2 split 4096 887)/2 = (389159663:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389159663:ℝ)/168755200)/ClassicalSixthBranch.v ((389159663:ℝ)/168755200) = (745476604703:ℝ)/378019466936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_886
  · change lowerPayment 887 ≤ lowerValue ((point 2 split 4096 887+point 2 split 4096 888)/2)
    have hp : lowerPayment 887 = (120630903857:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 887+point 2 split 4096 888)/2 = (15568717:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15568717:ℝ)/6750208)/ClassicalSixthBranch.v ((15568717:ℝ)/6750208) = (745399291029:ℝ)/377971459048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_887
  · change lowerPayment 888 ≤ lowerValue ((point 2 split 4096 888+point 2 split 4096 889)/2)
    have hp : lowerPayment 888 = (120745861243:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 888+point 2 split 4096 889)/2 = (389276187:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389276187:ℝ)/168755200)/ClassicalSixthBranch.v ((389276187:ℝ)/168755200) = (149064395471:ℝ)/75584690232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_888
  · change lowerPayment 889 ≤ lowerValue ((point 2 split 4096 889+point 2 split 4096 890)/2)
    have hp : lowerPayment 889 = (120860783078:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 889+point 2 split 4096 890)/2 = (389334449:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389334449:ℝ)/168755200)/ClassicalSixthBranch.v ((389334449:ℝ)/168755200) = (745244663681:ℝ)/377875443272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_889
  · change lowerPayment 890 ≤ lowerValue ((point 2 split 4096 890+point 2 split 4096 891)/2)
    have hp : lowerPayment 890 = (120975669393:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 890+point 2 split 4096 891)/2 = (389392711:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389392711:ℝ)/168755200)/ClassicalSixthBranch.v ((389392711:ℝ)/168755200) = (745167350007:ℝ)/377827435384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_890
  · change lowerPayment 891 ≤ lowerValue ((point 2 split 4096 891+point 2 split 4096 892)/2)
    have hp : lowerPayment 891 = (121090520222:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 891+point 2 split 4096 892)/2 = (389450973:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389450973:ℝ)/168755200)/ClassicalSixthBranch.v ((389450973:ℝ)/168755200) = (745090036333:ℝ)/377779427496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_891
  · change lowerPayment 892 ≤ lowerValue ((point 2 split 4096 892+point 2 split 4096 893)/2)
    have hp : lowerPayment 892 = (121205335596:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 892+point 2 split 4096 893)/2 = (77901847:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77901847:ℝ)/33751040)/ClassicalSixthBranch.v ((77901847:ℝ)/33751040) = (745012722659:ℝ)/377731419608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_892
  · change lowerPayment 893 ≤ lowerValue ((point 2 split 4096 893+point 2 split 4096 894)/2)
    have hp : lowerPayment 893 = (121320115547:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 893+point 2 split 4096 894)/2 = (389567497:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389567497:ℝ)/168755200)/ClassicalSixthBranch.v ((389567497:ℝ)/168755200) = (148987081797:ℝ)/75536682344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_893
  · change lowerPayment 894 ≤ lowerValue ((point 2 split 4096 894+point 2 split 4096 895)/2)
    have hp : lowerPayment 894 = (121434860108:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 894+point 2 split 4096 895)/2 = (389625759:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389625759:ℝ)/168755200)/ClassicalSixthBranch.v ((389625759:ℝ)/168755200) = (744858095311:ℝ)/377635403832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_894
  · change lowerPayment 895 ≤ lowerValue ((point 2 split 4096 895+point 2 split 4096 896)/2)
    have hp : lowerPayment 895 = (121549569311:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 895+point 2 split 4096 896)/2 = (389684021:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((389684021:ℝ)/168755200)/ClassicalSixthBranch.v ((389684021:ℝ)/168755200) = (744780781637:ℝ)/377587395944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_895
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_055
