import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints056
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_056 (j : Fin 16) : upperPayment (16*56+j.val) ≤
    upperValue ((point split endpoint 4096 (16*56+j.val)+point split endpoint 4096 (16*56+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 896 ≤ upperValue ((point split endpoint 4096 896+point split endpoint 4096 897)/2)
    have hp : upperPayment 896 = (367817437844:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 896+point split endpoint 4096 897)/2 = (598698527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598698527:ℝ)/168755200)*ClassicalSixthBranch.v ((598698527:ℝ)/168755200)/ClassicalSixthBranch.r = (140456697588305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_896
  · change upperPayment 897 ≤ upperValue ((point split endpoint 4096 897+point split endpoint 4096 898)/2)
    have hp : upperPayment 897 = (367745116954:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 897+point split endpoint 4096 898)/2 = (598723677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598723677:ℝ)/168755200)*ClassicalSixthBranch.v ((598723677:ℝ)/168755200)/ClassicalSixthBranch.r = (140432495864025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_897
  · change upperPayment 898 ≤ upperValue ((point split endpoint 4096 898+point split endpoint 4096 899)/2)
    have hp : upperPayment 898 = (367672774431:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 898+point split endpoint 4096 899)/2 = (598748827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598748827:ℝ)/168755200)*ClassicalSixthBranch.v ((598748827:ℝ)/168755200)/ClassicalSixthBranch.r = (140408296163817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_898
  · change upperPayment 899 ≤ upperValue ((point split endpoint 4096 899+point split endpoint 4096 900)/2)
    have hp : upperPayment 899 = (367600410271:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 899+point split endpoint 4096 900)/2 = (598773977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598773977:ℝ)/168755200)*ClassicalSixthBranch.v ((598773977:ℝ)/168755200)/ClassicalSixthBranch.r = (140384098487681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_899
  · change upperPayment 900 ≤ upperValue ((point split endpoint 4096 900+point split endpoint 4096 901)/2)
    have hp : upperPayment 900 = (367528024472:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 900+point split endpoint 4096 901)/2 = (598799127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598799127:ℝ)/168755200)*ClassicalSixthBranch.v ((598799127:ℝ)/168755200)/ClassicalSixthBranch.r = (140359902835617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_900
  · change upperPayment 901 ≤ upperValue ((point split endpoint 4096 901+point split endpoint 4096 902)/2)
    have hp : upperPayment 901 = (367455617030:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 901+point split endpoint 4096 902)/2 = (598824277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598824277:ℝ)/168755200)*ClassicalSixthBranch.v ((598824277:ℝ)/168755200)/ClassicalSixthBranch.r = (140335709207625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_901
  · change upperPayment 902 ≤ upperValue ((point split endpoint 4096 902+point split endpoint 4096 903)/2)
    have hp : upperPayment 902 = (367383187942:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 902+point split endpoint 4096 903)/2 = (598849427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598849427:ℝ)/168755200)*ClassicalSixthBranch.v ((598849427:ℝ)/168755200)/ClassicalSixthBranch.r = (140311517603705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_902
  · change upperPayment 903 ≤ upperValue ((point split endpoint 4096 903+point split endpoint 4096 904)/2)
    have hp : upperPayment 903 = (367310737204:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 903+point split endpoint 4096 904)/2 = (598874577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598874577:ℝ)/168755200)*ClassicalSixthBranch.v ((598874577:ℝ)/168755200)/ClassicalSixthBranch.r = (140287328023857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_903
  · change upperPayment 904 ≤ upperValue ((point split endpoint 4096 904+point split endpoint 4096 905)/2)
    have hp : upperPayment 904 = (367238264813:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 904+point split endpoint 4096 905)/2 = (598899727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598899727:ℝ)/168755200)*ClassicalSixthBranch.v ((598899727:ℝ)/168755200)/ClassicalSixthBranch.r = (140263140468081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_904
  · change upperPayment 905 ≤ upperValue ((point split endpoint 4096 905+point split endpoint 4096 906)/2)
    have hp : upperPayment 905 = (367165770766:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 905+point split endpoint 4096 906)/2 = (598924877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598924877:ℝ)/168755200)*ClassicalSixthBranch.v ((598924877:ℝ)/168755200)/ClassicalSixthBranch.r = (140238954936377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_905
  · change upperPayment 906 ≤ upperValue ((point split endpoint 4096 906+point split endpoint 4096 907)/2)
    have hp : upperPayment 906 = (367093255061:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 906+point split endpoint 4096 907)/2 = (598950027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598950027:ℝ)/168755200)*ClassicalSixthBranch.v ((598950027:ℝ)/168755200)/ClassicalSixthBranch.r = (140214771428745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_906
  · change upperPayment 907 ≤ upperValue ((point split endpoint 4096 907+point split endpoint 4096 908)/2)
    have hp : upperPayment 907 = (367020717692:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 907+point split endpoint 4096 908)/2 = (598975177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598975177:ℝ)/168755200)*ClassicalSixthBranch.v ((598975177:ℝ)/168755200)/ClassicalSixthBranch.r = (140190589945185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_907
  · change upperPayment 908 ≤ upperValue ((point split endpoint 4096 908+point split endpoint 4096 909)/2)
    have hp : upperPayment 908 = (366948158658:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 908+point split endpoint 4096 909)/2 = (599000327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599000327:ℝ)/168755200)*ClassicalSixthBranch.v ((599000327:ℝ)/168755200)/ClassicalSixthBranch.r = (140166410485697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_908
  · change upperPayment 909 ≤ upperValue ((point split endpoint 4096 909+point split endpoint 4096 910)/2)
    have hp : upperPayment 909 = (366875577955:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 909+point split endpoint 4096 910)/2 = (599025477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599025477:ℝ)/168755200)*ClassicalSixthBranch.v ((599025477:ℝ)/168755200)/ClassicalSixthBranch.r = (140142233050281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_909
  · change upperPayment 910 ≤ upperValue ((point split endpoint 4096 910+point split endpoint 4096 911)/2)
    have hp : upperPayment 910 = (366802975579:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 910+point split endpoint 4096 911)/2 = (599050627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599050627:ℝ)/168755200)*ClassicalSixthBranch.v ((599050627:ℝ)/168755200)/ClassicalSixthBranch.r = (140118057638937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_910
  · change upperPayment 911 ≤ upperValue ((point split endpoint 4096 911+point split endpoint 4096 912)/2)
    have hp : upperPayment 911 = (366730351528:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 911+point split endpoint 4096 912)/2 = (599075777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599075777:ℝ)/168755200)*ClassicalSixthBranch.v ((599075777:ℝ)/168755200)/ClassicalSixthBranch.r = (140093884251665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_911
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_056
