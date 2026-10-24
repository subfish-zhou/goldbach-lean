import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints061
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_061 (j : Fin 16) : lowerPayment (16*61+j.val) ≤
    lowerValue ((point 2 split 4096 (16*61+j.val)+point 2 split 4096 (16*61+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 976 ≤ lowerValue ((point 2 split 4096 976+point 2 split 4096 977)/2)
    have hp : lowerPayment 976 = (130726493729:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 976+point 2 split 4096 977)/2 = (394403243:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394403243:ℝ)/168755200)/ClassicalSixthBranch.v ((394403243:ℝ)/168755200) = (738518374043:ℝ)/373698757016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_976
  · change lowerPayment 977 ≤ lowerValue ((point 2 split 4096 977+point 2 split 4096 978)/2)
    have hp : lowerPayment 977 = (130838410535:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 977+point 2 split 4096 978)/2 = (78892301:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78892301:ℝ)/33751040)/ClassicalSixthBranch.v ((78892301:ℝ)/33751040) = (738441060369:ℝ)/373650749128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_977
  · change lowerPayment 978 ≤ lowerValue ((point 2 split 4096 978+point 2 split 4096 979)/2)
    have hp : lowerPayment 978 = (130950294564:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 978+point 2 split 4096 979)/2 = (3830289:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((3830289:ℝ)/1638400)/ClassicalSixthBranch.v ((3830289:ℝ)/1638400) = (1433716013:ℝ)/725442216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_978
  · change lowerPayment 979 ≤ lowerValue ((point 2 split 4096 979+point 2 split 4096 980)/2)
    have hp : lowerPayment 979 = (131062145847:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 979+point 2 split 4096 980)/2 = (394578029:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394578029:ℝ)/168755200)/ClassicalSixthBranch.v ((394578029:ℝ)/168755200) = (738286433021:ℝ)/373554733352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_979
  · change lowerPayment 980 ≤ lowerValue ((point 2 split 4096 980+point 2 split 4096 981)/2)
    have hp : lowerPayment 980 = (131173964413:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 980+point 2 split 4096 981)/2 = (394636291:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394636291:ℝ)/168755200)/ClassicalSixthBranch.v ((394636291:ℝ)/168755200) = (738209119347:ℝ)/373506725464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_980
  · change lowerPayment 981 ≤ lowerValue ((point 2 split 4096 981+point 2 split 4096 982)/2)
    have hp : lowerPayment 981 = (131285750294:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 981+point 2 split 4096 982)/2 = (394694553:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394694553:ℝ)/168755200)/ClassicalSixthBranch.v ((394694553:ℝ)/168755200) = (738131805673:ℝ)/373458717576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_981
  · change lowerPayment 982 ≤ lowerValue ((point 2 split 4096 982+point 2 split 4096 983)/2)
    have hp : lowerPayment 982 = (131397503518:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 982+point 2 split 4096 983)/2 = (78950563:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78950563:ℝ)/33751040)/ClassicalSixthBranch.v ((78950563:ℝ)/33751040) = (738054491999:ℝ)/373410709688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_982
  · change lowerPayment 983 ≤ lowerValue ((point 2 split 4096 983+point 2 split 4096 984)/2)
    have hp : lowerPayment 983 = (131509224116:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 983+point 2 split 4096 984)/2 = (394811077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394811077:ℝ)/168755200)/ClassicalSixthBranch.v ((394811077:ℝ)/168755200) = (29519087133:ℝ)/14934508072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_983
  · change lowerPayment 984 ≤ lowerValue ((point 2 split 4096 984+point 2 split 4096 985)/2)
    have hp : lowerPayment 984 = (131620912118:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 984+point 2 split 4096 985)/2 = (394869339:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394869339:ℝ)/168755200)/ClassicalSixthBranch.v ((394869339:ℝ)/168755200) = (737899864651:ℝ)/373314693912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_984
  · change lowerPayment 985 ≤ lowerValue ((point 2 split 4096 985+point 2 split 4096 986)/2)
    have hp : lowerPayment 985 = (131732567554:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 985+point 2 split 4096 986)/2 = (394927601:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394927601:ℝ)/168755200)/ClassicalSixthBranch.v ((394927601:ℝ)/168755200) = (737822550977:ℝ)/373266686024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_985
  · change lowerPayment 986 ≤ lowerValue ((point 2 split 4096 986+point 2 split 4096 987)/2)
    have hp : lowerPayment 986 = (131844190454:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 986+point 2 split 4096 987)/2 = (394985863:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394985863:ℝ)/168755200)/ClassicalSixthBranch.v ((394985863:ℝ)/168755200) = (737745237303:ℝ)/373218678136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_986
  · change lowerPayment 987 ≤ lowerValue ((point 2 split 4096 987+point 2 split 4096 988)/2)
    have hp : lowerPayment 987 = (131955780848:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 987+point 2 split 4096 988)/2 = (15801765:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15801765:ℝ)/6750208)/ClassicalSixthBranch.v ((15801765:ℝ)/6750208) = (737667923629:ℝ)/373170670248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_987
  · change lowerPayment 988 ≤ lowerValue ((point 2 split 4096 988+point 2 split 4096 989)/2)
    have hp : lowerPayment 988 = (132067338766:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 988+point 2 split 4096 989)/2 = (395102387:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395102387:ℝ)/168755200)/ClassicalSixthBranch.v ((395102387:ℝ)/168755200) = (147518121991:ℝ)/74624532472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_988
  · change lowerPayment 989 ≤ lowerValue ((point 2 split 4096 989+point 2 split 4096 990)/2)
    have hp : lowerPayment 989 = (132178864237:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 989+point 2 split 4096 990)/2 = (395160649:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395160649:ℝ)/168755200)/ClassicalSixthBranch.v ((395160649:ℝ)/168755200) = (737513296281:ℝ)/373074654472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_989
  · change lowerPayment 990 ≤ lowerValue ((point 2 split 4096 990+point 2 split 4096 991)/2)
    have hp : lowerPayment 990 = (132290357293:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 990+point 2 split 4096 991)/2 = (395218911:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395218911:ℝ)/168755200)/ClassicalSixthBranch.v ((395218911:ℝ)/168755200) = (737435982607:ℝ)/373026646584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_990
  · change lowerPayment 991 ≤ lowerValue ((point 2 split 4096 991+point 2 split 4096 992)/2)
    have hp : lowerPayment 991 = (132401817961:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 991+point 2 split 4096 992)/2 = (395277173:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((395277173:ℝ)/168755200)/ClassicalSixthBranch.v ((395277173:ℝ)/168755200) = (737358668933:ℝ)/372978638696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_991
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_061
