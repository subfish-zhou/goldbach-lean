import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints247
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_247 (j : Fin 16) : lowerPayment (16*247+j.val) ≤
    lowerValue ((point 2 split 4096 (16*247+j.val)+point 2 split 4096 (16*247+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3952 ≤ lowerValue ((point 2 split 4096 3952+point 2 split 4096 3953)/2)
    have hp : lowerPayment 3952 = (409780127051:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3952+point 2 split 4096 3953)/2 = (113558191:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113558191:ℝ)/33751040)/ClassicalSixthBranch.v ((113558191:ℝ)/33751040) = (508432880219:ℝ)/230827282328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3952
  · change lowerPayment 3953 ≤ lowerValue ((point 2 split 4096 3953+point 2 split 4096 3954)/2)
    have hp : lowerPayment 3953 = (409879887703:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3953+point 2 split 4096 3954)/2 = (567849217:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567849217:ℝ)/168755200)/ClassicalSixthBranch.v ((567849217:ℝ)/168755200) = (101671113309:ℝ)/46155854888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3953
  · change lowerPayment 3954 ≤ lowerValue ((point 2 split 4096 3954+point 2 split 4096 3955)/2)
    have hp : lowerPayment 3954 = (409979667984:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3954+point 2 split 4096 3955)/2 = (567907479:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567907479:ℝ)/168755200)/ClassicalSixthBranch.v ((567907479:ℝ)/168755200) = (508278252871:ℝ)/230731266552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3954
  · change lowerPayment 3955 ≤ lowerValue ((point 2 split 4096 3955+point 2 split 4096 3956)/2)
    have hp : lowerPayment 3955 = (410079467912:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3955+point 2 split 4096 3956)/2 = (567965741:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((567965741:ℝ)/168755200)/ClassicalSixthBranch.v ((567965741:ℝ)/168755200) = (508200939197:ℝ)/230683258664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3955
  · change lowerPayment 3956 ≤ lowerValue ((point 2 split 4096 3956+point 2 split 4096 3957)/2)
    have hp : lowerPayment 3956 = (410179287506:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3956+point 2 split 4096 3957)/2 = (568024003:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((568024003:ℝ)/168755200)/ClassicalSixthBranch.v ((568024003:ℝ)/168755200) = (508123625523:ℝ)/230635250776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3956
  · change lowerPayment 3957 ≤ lowerValue ((point 2 split 4096 3957+point 2 split 4096 3958)/2)
    have hp : lowerPayment 3957 = (410279126785:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3957+point 2 split 4096 3958)/2 = (113616453:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113616453:ℝ)/33751040)/ClassicalSixthBranch.v ((113616453:ℝ)/33751040) = (508046311849:ℝ)/230587242888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3957
  · change lowerPayment 3958 ≤ lowerValue ((point 2 split 4096 3958+point 2 split 4096 3959)/2)
    have hp : lowerPayment 3958 = (410378985767:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3958+point 2 split 4096 3959)/2 = (568140527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((568140527:ℝ)/168755200)/ClassicalSixthBranch.v ((568140527:ℝ)/168755200) = (20318759927:ℝ)/9221569400 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3958
  · change lowerPayment 3959 ≤ lowerValue ((point 2 split 4096 3959+point 2 split 4096 3960)/2)
    have hp : lowerPayment 3959 = (410478864471:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3959+point 2 split 4096 3960)/2 = (568198789:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((568198789:ℝ)/168755200)/ClassicalSixthBranch.v ((568198789:ℝ)/168755200) = (507891684501:ℝ)/230491227112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3959
  · change lowerPayment 3960 ≤ lowerValue ((point 2 split 4096 3960+point 2 split 4096 3961)/2)
    have hp : lowerPayment 3960 = (410578762914:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3960+point 2 split 4096 3961)/2 = (568257051:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((568257051:ℝ)/168755200)/ClassicalSixthBranch.v ((568257051:ℝ)/168755200) = (507814370827:ℝ)/230443219224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3960
  · change lowerPayment 3961 ≤ lowerValue ((point 2 split 4096 3961+point 2 split 4096 3962)/2)
    have hp : lowerPayment 3961 = (410678681116:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3961+point 2 split 4096 3962)/2 = (568315313:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((568315313:ℝ)/168755200)/ClassicalSixthBranch.v ((568315313:ℝ)/168755200) = (507737057153:ℝ)/230395211336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3961
  · change lowerPayment 3962 ≤ lowerValue ((point 2 split 4096 3962+point 2 split 4096 3963)/2)
    have hp : lowerPayment 3962 = (410778619096:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3962+point 2 split 4096 3963)/2 = (22734943:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22734943:ℝ)/6750208)/ClassicalSixthBranch.v ((22734943:ℝ)/6750208) = (507659743479:ℝ)/230347203448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3962
  · change lowerPayment 3963 ≤ lowerValue ((point 2 split 4096 3963+point 2 split 4096 3964)/2)
    have hp : lowerPayment 3963 = (410878576871:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3963+point 2 split 4096 3964)/2 = (568431837:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((568431837:ℝ)/168755200)/ClassicalSixthBranch.v ((568431837:ℝ)/168755200) = (101516485961:ℝ)/46059839112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3963
  · change lowerPayment 3964 ≤ lowerValue ((point 2 split 4096 3964+point 2 split 4096 3965)/2)
    have hp : lowerPayment 3964 = (410978554460:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3964+point 2 split 4096 3965)/2 = (568490099:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((568490099:ℝ)/168755200)/ClassicalSixthBranch.v ((568490099:ℝ)/168755200) = (507505116131:ℝ)/230251187672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3964
  · change lowerPayment 3965 ≤ lowerValue ((point 2 split 4096 3965+point 2 split 4096 3966)/2)
    have hp : lowerPayment 3965 = (411078551882:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3965+point 2 split 4096 3966)/2 = (5519887:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((5519887:ℝ)/1638400)/ClassicalSixthBranch.v ((5519887:ℝ)/1638400) = (4926483519:ℝ)/2234982328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3965
  · change lowerPayment 3966 ≤ lowerValue ((point 2 split 4096 3966+point 2 split 4096 3967)/2)
    have hp : lowerPayment 3966 = (411178569156:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3966+point 2 split 4096 3967)/2 = (568606623:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((568606623:ℝ)/168755200)/ClassicalSixthBranch.v ((568606623:ℝ)/168755200) = (507350488783:ℝ)/230155171896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3966
  · change lowerPayment 3967 ≤ lowerValue ((point 2 split 4096 3967+point 2 split 4096 3968)/2)
    have hp : lowerPayment 3967 = (411278606299:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3967+point 2 split 4096 3968)/2 = (113732977:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113732977:ℝ)/33751040)/ClassicalSixthBranch.v ((113732977:ℝ)/33751040) = (507273175109:ℝ)/230107164008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3967
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_247
