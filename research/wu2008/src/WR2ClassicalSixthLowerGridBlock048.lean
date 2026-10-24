import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints048
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_048 (j : Fin 16) : lowerPayment (16*48+j.val) ≤
    lowerValue ((point 2 split 4096 (16*48+j.val)+point 2 split 4096 (16*48+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 768 ≤ lowerValue ((point 2 split 4096 768+point 2 split 4096 769)/2)
    have hp : lowerPayment 768 = (106687625959:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 768+point 2 split 4096 769)/2 = (382284747:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382284747:ℝ)/168755200)/ClassicalSixthBranch.v ((382284747:ℝ)/168755200) = (150919923647:ℝ)/76736879544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_768
  · change lowerPayment 769 ≤ lowerValue ((point 2 split 4096 769+point 2 split 4096 770)/2)
    have hp : lowerPayment 769 = (106807051656:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 769+point 2 split 4096 770)/2 = (382343009:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382343009:ℝ)/168755200)/ClassicalSixthBranch.v ((382343009:ℝ)/168755200) = (754522304561:ℝ)/383636389832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_769
  · change lowerPayment 770 ≤ lowerValue ((point 2 split 4096 770+point 2 split 4096 771)/2)
    have hp : lowerPayment 770 = (106926437777:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 770+point 2 split 4096 771)/2 = (382401271:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382401271:ℝ)/168755200)/ClassicalSixthBranch.v ((382401271:ℝ)/168755200) = (754444990887:ℝ)/383588381944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_770
  · change lowerPayment 771 ≤ lowerValue ((point 2 split 4096 771+point 2 split 4096 772)/2)
    have hp : lowerPayment 771 = (107045784358:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 771+point 2 split 4096 772)/2 = (382459533:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382459533:ℝ)/168755200)/ClassicalSixthBranch.v ((382459533:ℝ)/168755200) = (754367677213:ℝ)/383540374056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_771
  · change lowerPayment 772 ≤ lowerValue ((point 2 split 4096 772+point 2 split 4096 773)/2)
    have hp : lowerPayment 772 = (107165091434:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 772+point 2 split 4096 773)/2 = (742753:ℝ)/327680 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((742753:ℝ)/327680)/ClassicalSixthBranch.v ((742753:ℝ)/327680) = (7323207413:ℝ)/3723226856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_772
  · change lowerPayment 773 ≤ lowerValue ((point 2 split 4096 773+point 2 split 4096 774)/2)
    have hp : lowerPayment 773 = (107284359040:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 773+point 2 split 4096 774)/2 = (382576057:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382576057:ℝ)/168755200)/ClassicalSixthBranch.v ((382576057:ℝ)/168755200) = (150842609973:ℝ)/76688871656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_773
  · change lowerPayment 774 ≤ lowerValue ((point 2 split 4096 774+point 2 split 4096 775)/2)
    have hp : lowerPayment 774 = (107403587211:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 774+point 2 split 4096 775)/2 = (382634319:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382634319:ℝ)/168755200)/ClassicalSixthBranch.v ((382634319:ℝ)/168755200) = (754135736191:ℝ)/383396350392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_774
  · change lowerPayment 775 ≤ lowerValue ((point 2 split 4096 775+point 2 split 4096 776)/2)
    have hp : lowerPayment 775 = (107522775984:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 775+point 2 split 4096 776)/2 = (382692581:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382692581:ℝ)/168755200)/ClassicalSixthBranch.v ((382692581:ℝ)/168755200) = (754058422517:ℝ)/383348342504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_775
  · change lowerPayment 776 ≤ lowerValue ((point 2 split 4096 776+point 2 split 4096 777)/2)
    have hp : lowerPayment 776 = (107641925393:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 776+point 2 split 4096 777)/2 = (382750843:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382750843:ℝ)/168755200)/ClassicalSixthBranch.v ((382750843:ℝ)/168755200) = (753981108843:ℝ)/383300334616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_776
  · change lowerPayment 777 ≤ lowerValue ((point 2 split 4096 777+point 2 split 4096 778)/2)
    have hp : lowerPayment 777 = (107761035474:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 777+point 2 split 4096 778)/2 = (76561821:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((76561821:ℝ)/33751040)/ClassicalSixthBranch.v ((76561821:ℝ)/33751040) = (753903795169:ℝ)/383252326728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_777
  · change lowerPayment 778 ≤ lowerValue ((point 2 split 4096 778+point 2 split 4096 779)/2)
    have hp : lowerPayment 778 = (107880106262:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 778+point 2 split 4096 779)/2 = (382867367:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382867367:ℝ)/168755200)/ClassicalSixthBranch.v ((382867367:ℝ)/168755200) = (113613637:ℝ)/57754984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_778
  · change lowerPayment 779 ≤ lowerValue ((point 2 split 4096 779+point 2 split 4096 780)/2)
    have hp : lowerPayment 779 = (107999137791:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 779+point 2 split 4096 780)/2 = (382925629:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382925629:ℝ)/168755200)/ClassicalSixthBranch.v ((382925629:ℝ)/168755200) = (753749167821:ℝ)/383156310952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_779
  · change lowerPayment 780 ≤ lowerValue ((point 2 split 4096 780+point 2 split 4096 781)/2)
    have hp : lowerPayment 780 = (108118130098:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 780+point 2 split 4096 781)/2 = (382983891:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((382983891:ℝ)/168755200)/ClassicalSixthBranch.v ((382983891:ℝ)/168755200) = (753671854147:ℝ)/383108303064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_780
  · change lowerPayment 781 ≤ lowerValue ((point 2 split 4096 781+point 2 split 4096 782)/2)
    have hp : lowerPayment 781 = (108237083217:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 781+point 2 split 4096 782)/2 = (383042153:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383042153:ℝ)/168755200)/ClassicalSixthBranch.v ((383042153:ℝ)/168755200) = (753594540473:ℝ)/383060295176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_781
  · change lowerPayment 782 ≤ lowerValue ((point 2 split 4096 782+point 2 split 4096 783)/2)
    have hp : lowerPayment 782 = (108355997184:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 782+point 2 split 4096 783)/2 = (76620083:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((76620083:ℝ)/33751040)/ClassicalSixthBranch.v ((76620083:ℝ)/33751040) = (753517226799:ℝ)/383012287288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_782
  · change lowerPayment 783 ≤ lowerValue ((point 2 split 4096 783+point 2 split 4096 784)/2)
    have hp : lowerPayment 783 = (108474872034:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 783+point 2 split 4096 784)/2 = (383158677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((383158677:ℝ)/168755200)/ClassicalSixthBranch.v ((383158677:ℝ)/168755200) = (30137596525:ℝ)/15318571176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_783
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_048
