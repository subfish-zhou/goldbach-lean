import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints048
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_048 (j : Fin 16) : initialPayment (16*48+j.val) ≤
    initialValue ((point lo 4 1024 (16*48+j.val)+point lo 4 1024 (16*48+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 768 ≤ initialValue ((point lo 4 1024 768+point lo 4 1024 769)/2)
    have hp : initialPayment 768 = (413990696897:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 768+point lo 4 1024 769)/2 = (162587941:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162587941:ℝ)/42188800) = (67942400:ℝ)/49392347 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_768
  · change initialPayment 769 ≤ initialValue ((point lo 4 1024 769+point lo 4 1024 770)/2)
    have hp : initialPayment 769 = (414728362814:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 769+point lo 4 1024 770)/2 = (162612079:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162612079:ℝ)/42188800) = (67942400:ℝ)/49368209 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_769
  · change initialPayment 770 ≤ initialValue ((point lo 4 1024 770+point lo 4 1024 771)/2)
    have hp : initialPayment 770 = (415466675930:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 770+point lo 4 1024 771)/2 = (162636217:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162636217:ℝ)/42188800) = (67942400:ℝ)/49344071 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_770
  · change initialPayment 771 ≤ initialValue ((point lo 4 1024 771+point lo 4 1024 772)/2)
    have hp : initialPayment 771 = (416205636907:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 771+point lo 4 1024 772)/2 = (32532071:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32532071:ℝ)/8437760) = (67942400:ℝ)/49319933 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_771
  · change initialPayment 772 ≤ initialValue ((point lo 4 1024 772+point lo 4 1024 773)/2)
    have hp : initialPayment 772 = (416945246408:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 772+point lo 4 1024 773)/2 = (162684493:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162684493:ℝ)/42188800) = (13588480:ℝ)/9859159 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_772
  · change initialPayment 773 ≤ initialValue ((point lo 4 1024 773+point lo 4 1024 774)/2)
    have hp : initialPayment 773 = (417685505096:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 773+point lo 4 1024 774)/2 = (162708631:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162708631:ℝ)/42188800) = (67942400:ℝ)/49271657 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_773
  · change initialPayment 774 ≤ initialValue ((point lo 4 1024 774+point lo 4 1024 775)/2)
    have hp : initialPayment 774 = (418426413638:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 774+point lo 4 1024 775)/2 = (162732769:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162732769:ℝ)/42188800) = (67942400:ℝ)/49247519 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_774
  · change initialPayment 775 ≤ initialValue ((point lo 4 1024 775+point lo 4 1024 776)/2)
    have hp : initialPayment 775 = (419167972700:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 775+point lo 4 1024 776)/2 = (162756907:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162756907:ℝ)/42188800) = (67942400:ℝ)/49223381 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_775
  · change initialPayment 776 ≤ initialValue ((point lo 4 1024 776+point lo 4 1024 777)/2)
    have hp : initialPayment 776 = (419910182947:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 776+point lo 4 1024 777)/2 = (32556209:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32556209:ℝ)/8437760) = (67942400:ℝ)/49199243 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_776
  · change initialPayment 777 ≤ initialValue ((point lo 4 1024 777+point lo 4 1024 778)/2)
    have hp : initialPayment 777 = (420653045050:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 777+point lo 4 1024 778)/2 = (162805183:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162805183:ℝ)/42188800) = (13588480:ℝ)/9835021 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_777
  · change initialPayment 778 ≤ initialValue ((point lo 4 1024 778+point lo 4 1024 779)/2)
    have hp : initialPayment 778 = (421396559677:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 778+point lo 4 1024 779)/2 = (162829321:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162829321:ℝ)/42188800) = (67942400:ℝ)/49150967 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_778
  · change initialPayment 779 ≤ initialValue ((point lo 4 1024 779+point lo 4 1024 780)/2)
    have hp : initialPayment 779 = (422140727498:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 779+point lo 4 1024 780)/2 = (162853459:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162853459:ℝ)/42188800) = (67942400:ℝ)/49126829 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_779
  · change initialPayment 780 ≤ initialValue ((point lo 4 1024 780+point lo 4 1024 781)/2)
    have hp : initialPayment 780 = (422885549185:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 780+point lo 4 1024 781)/2 = (162877597:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162877597:ℝ)/42188800) = (67942400:ℝ)/49102691 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_780
  · change initialPayment 781 ≤ initialValue ((point lo 4 1024 781+point lo 4 1024 782)/2)
    have hp : initialPayment 781 = (423631025410:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 781+point lo 4 1024 782)/2 = (32580347:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32580347:ℝ)/8437760) = (67942400:ℝ)/49078553 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_781
  · change initialPayment 782 ≤ initialValue ((point lo 4 1024 782+point lo 4 1024 783)/2)
    have hp : initialPayment 782 = (424377156847:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 782+point lo 4 1024 783)/2 = (162925873:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162925873:ℝ)/42188800) = (13588480:ℝ)/9810883 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_782
  · change initialPayment 783 ≤ initialValue ((point lo 4 1024 783+point lo 4 1024 784)/2)
    have hp : initialPayment 783 = (425123944171:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 783+point lo 4 1024 784)/2 = (162950011:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((162950011:ℝ)/42188800) = (67942400:ℝ)/49030277 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_783
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_048
