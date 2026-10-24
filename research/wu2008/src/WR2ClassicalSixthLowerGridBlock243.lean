import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints243
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_243 (j : Fin 16) : lowerPayment (16*243+j.val) ≤
    lowerValue ((point 2 split 4096 (16*243+j.val)+point 2 split 4096 (16*243+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3888 ≤ lowerValue ((point 2 split 4096 3888+point 2 split 4096 3889)/2)
    have hp : lowerPayment 3888 = (403435434573:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3888+point 2 split 4096 3889)/2 = (564062187:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564062187:ℝ)/168755200)/ClassicalSixthBranch.v ((564062187:ℝ)/168755200) = (102676191071:ℝ)/46779957432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3888
  · change lowerPayment 3889 ≤ lowerValue ((point 2 split 4096 3889+point 2 split 4096 3890)/2)
    have hp : lowerPayment 3889 = (403533977017:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3889+point 2 split 4096 3890)/2 = (564120449:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564120449:ℝ)/168755200)/ClassicalSixthBranch.v ((564120449:ℝ)/168755200) = (513303641681:ℝ)/233851779272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3889
  · change lowerPayment 3890 ≤ lowerValue ((point 2 split 4096 3890+point 2 split 4096 3891)/2)
    have hp : lowerPayment 3890 = (403632537925:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3890+point 2 split 4096 3891)/2 = (564178711:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564178711:ℝ)/168755200)/ClassicalSixthBranch.v ((564178711:ℝ)/168755200) = (513226328007:ℝ)/233803771384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3890
  · change lowerPayment 3891 ≤ lowerValue ((point 2 split 4096 3891+point 2 split 4096 3892)/2)
    have hp : lowerPayment 3891 = (403731117316:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3891+point 2 split 4096 3892)/2 = (564236973:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564236973:ℝ)/168755200)/ClassicalSixthBranch.v ((564236973:ℝ)/168755200) = (513149014333:ℝ)/233755763496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3891
  · change lowerPayment 3892 ≤ lowerValue ((point 2 split 4096 3892+point 2 split 4096 3893)/2)
    have hp : lowerPayment 3892 = (403829715206:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3892+point 2 split 4096 3893)/2 = (112859047:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112859047:ℝ)/33751040)/ClassicalSixthBranch.v ((112859047:ℝ)/33751040) = (513071700659:ℝ)/233707755608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3892
  · change lowerPayment 3893 ≤ lowerValue ((point 2 split 4096 3893+point 2 split 4096 3894)/2)
    have hp : lowerPayment 3893 = (403928331613:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3893+point 2 split 4096 3894)/2 = (564353497:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564353497:ℝ)/168755200)/ClassicalSixthBranch.v ((564353497:ℝ)/168755200) = (102598877397:ℝ)/46731949544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3893
  · change lowerPayment 3894 ≤ lowerValue ((point 2 split 4096 3894+point 2 split 4096 3895)/2)
    have hp : lowerPayment 3894 = (404026966557:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3894+point 2 split 4096 3895)/2 = (564411759:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564411759:ℝ)/168755200)/ClassicalSixthBranch.v ((564411759:ℝ)/168755200) = (512917073311:ℝ)/233611739832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3894
  · change lowerPayment 3895 ≤ lowerValue ((point 2 split 4096 3895+point 2 split 4096 3896)/2)
    have hp : lowerPayment 3895 = (404125620054:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3895+point 2 split 4096 3896)/2 = (564470021:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564470021:ℝ)/168755200)/ClassicalSixthBranch.v ((564470021:ℝ)/168755200) = (512839759637:ℝ)/233563731944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3895
  · change lowerPayment 3896 ≤ lowerValue ((point 2 split 4096 3896+point 2 split 4096 3897)/2)
    have hp : lowerPayment 3896 = (404224292123:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3896+point 2 split 4096 3897)/2 = (564528283:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564528283:ℝ)/168755200)/ClassicalSixthBranch.v ((564528283:ℝ)/168755200) = (512762445963:ℝ)/233515724056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3896
  · change lowerPayment 3897 ≤ lowerValue ((point 2 split 4096 3897+point 2 split 4096 3898)/2)
    have hp : lowerPayment 3897 = (404322982781:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3897+point 2 split 4096 3898)/2 = (112917309:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112917309:ℝ)/33751040)/ClassicalSixthBranch.v ((112917309:ℝ)/33751040) = (512685132289:ℝ)/233467716168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3897
  · change lowerPayment 3898 ≤ lowerValue ((point 2 split 4096 3898+point 2 split 4096 3899)/2)
    have hp : lowerPayment 3898 = (404421692047:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3898+point 2 split 4096 3899)/2 = (564644807:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564644807:ℝ)/168755200)/ClassicalSixthBranch.v ((564644807:ℝ)/168755200) = (102521563723:ℝ)/46683941656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3898
  · change lowerPayment 3899 ≤ lowerValue ((point 2 split 4096 3899+point 2 split 4096 3900)/2)
    have hp : lowerPayment 3899 = (404520419939:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3899+point 2 split 4096 3900)/2 = (564703069:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564703069:ℝ)/168755200)/ClassicalSixthBranch.v ((564703069:ℝ)/168755200) = (512530504941:ℝ)/233371700392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3899
  · change lowerPayment 3900 ≤ lowerValue ((point 2 split 4096 3900+point 2 split 4096 3901)/2)
    have hp : lowerPayment 3900 = (404619166475:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3900+point 2 split 4096 3901)/2 = (564761331:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564761331:ℝ)/168755200)/ClassicalSixthBranch.v ((564761331:ℝ)/168755200) = (512453191267:ℝ)/233323692504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3900
  · change lowerPayment 3901 ≤ lowerValue ((point 2 split 4096 3901+point 2 split 4096 3902)/2)
    have hp : lowerPayment 3901 = (404717931672:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3901+point 2 split 4096 3902)/2 = (564819593:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564819593:ℝ)/168755200)/ClassicalSixthBranch.v ((564819593:ℝ)/168755200) = (512375877593:ℝ)/233275684616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3901
  · change lowerPayment 3902 ≤ lowerValue ((point 2 split 4096 3902+point 2 split 4096 3903)/2)
    have hp : lowerPayment 3902 = (404816715549:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3902+point 2 split 4096 3903)/2 = (112975571:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112975571:ℝ)/33751040)/ClassicalSixthBranch.v ((112975571:ℝ)/33751040) = (512298563919:ℝ)/233227676728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3902
  · change lowerPayment 3903 ≤ lowerValue ((point 2 split 4096 3903+point 2 split 4096 3904)/2)
    have hp : lowerPayment 3903 = (404915518124:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3903+point 2 split 4096 3904)/2 = (564936117:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((564936117:ℝ)/168755200)/ClassicalSixthBranch.v ((564936117:ℝ)/168755200) = (102444250049:ℝ)/46635933768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3903
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_243
