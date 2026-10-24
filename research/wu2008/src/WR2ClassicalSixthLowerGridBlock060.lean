import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints060
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_060 (j : Fin 16) : lowerPayment (16*60+j.val) ≤
    lowerValue ((point 2 split 4096 (16*60+j.val)+point 2 split 4096 (16*60+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 960 ≤ lowerValue ((point 2 split 4096 960+point 2 split 4096 961)/2)
    have hp : lowerPayment 960 = (128931342570:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 960+point 2 split 4096 961)/2 = (393471051:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393471051:ℝ)/168755200)/ClassicalSixthBranch.v ((393471051:ℝ)/168755200) = (739755392827:ℝ)/374466883224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_960
  · change lowerPayment 961 ≤ lowerValue ((point 2 split 4096 961+point 2 split 4096 962)/2)
    have hp : lowerPayment 961 = (129043787915:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 961+point 2 split 4096 962)/2 = (393529313:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393529313:ℝ)/168755200)/ClassicalSixthBranch.v ((393529313:ℝ)/168755200) = (739678079153:ℝ)/374418875336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_961
  · change lowerPayment 962 ≤ lowerValue ((point 2 split 4096 962+point 2 split 4096 963)/2)
    have hp : lowerPayment 962 = (129156199998:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 962+point 2 split 4096 963)/2 = (15743503:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15743503:ℝ)/6750208)/ClassicalSixthBranch.v ((15743503:ℝ)/6750208) = (739600765479:ℝ)/374370867448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_962
  · change lowerPayment 963 ≤ lowerValue ((point 2 split 4096 963+point 2 split 4096 964)/2)
    have hp : lowerPayment 963 = (129268578850:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 963+point 2 split 4096 964)/2 = (393645837:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393645837:ℝ)/168755200)/ClassicalSixthBranch.v ((393645837:ℝ)/168755200) = (147904690361:ℝ)/74864571912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_963
  · change lowerPayment 964 ≤ lowerValue ((point 2 split 4096 964+point 2 split 4096 965)/2)
    have hp : lowerPayment 964 = (129380924502:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 964+point 2 split 4096 965)/2 = (393704099:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393704099:ℝ)/168755200)/ClassicalSixthBranch.v ((393704099:ℝ)/168755200) = (739446138131:ℝ)/374274851672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_964
  · change lowerPayment 965 ≤ lowerValue ((point 2 split 4096 965+point 2 split 4096 966)/2)
    have hp : lowerPayment 965 = (129493236983:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 965+point 2 split 4096 966)/2 = (393762361:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393762361:ℝ)/168755200)/ClassicalSixthBranch.v ((393762361:ℝ)/168755200) = (739368824457:ℝ)/374226843784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_965
  · change lowerPayment 966 ≤ lowerValue ((point 2 split 4096 966+point 2 split 4096 967)/2)
    have hp : lowerPayment 966 = (129605516325:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 966+point 2 split 4096 967)/2 = (393820623:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393820623:ℝ)/168755200)/ClassicalSixthBranch.v ((393820623:ℝ)/168755200) = (739291510783:ℝ)/374178835896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_966
  · change lowerPayment 967 ≤ lowerValue ((point 2 split 4096 967+point 2 split 4096 968)/2)
    have hp : lowerPayment 967 = (129717762557:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 967+point 2 split 4096 968)/2 = (78775777:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78775777:ℝ)/33751040)/ClassicalSixthBranch.v ((78775777:ℝ)/33751040) = (739214197109:ℝ)/374130828008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_967
  · change lowerPayment 968 ≤ lowerValue ((point 2 split 4096 968+point 2 split 4096 969)/2)
    have hp : lowerPayment 968 = (129829975710:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 968+point 2 split 4096 969)/2 = (393937147:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393937147:ℝ)/168755200)/ClassicalSixthBranch.v ((393937147:ℝ)/168755200) = (147827376687:ℝ)/74816564024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_968
  · change lowerPayment 969 ≤ lowerValue ((point 2 split 4096 969+point 2 split 4096 970)/2)
    have hp : lowerPayment 969 = (129942155814:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 969+point 2 split 4096 970)/2 = (393995409:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((393995409:ℝ)/168755200)/ClassicalSixthBranch.v ((393995409:ℝ)/168755200) = (739059569761:ℝ)/374034812232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_969
  · change lowerPayment 970 ≤ lowerValue ((point 2 split 4096 970+point 2 split 4096 971)/2)
    have hp : lowerPayment 970 = (130054302901:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 970+point 2 split 4096 971)/2 = (394053671:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394053671:ℝ)/168755200)/ClassicalSixthBranch.v ((394053671:ℝ)/168755200) = (738982256087:ℝ)/373986804344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_970
  · change lowerPayment 971 ≤ lowerValue ((point 2 split 4096 971+point 2 split 4096 972)/2)
    have hp : lowerPayment 971 = (130166416999:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 971+point 2 split 4096 972)/2 = (394111933:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394111933:ℝ)/168755200)/ClassicalSixthBranch.v ((394111933:ℝ)/168755200) = (738904942413:ℝ)/373938796456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_971
  · change lowerPayment 972 ≤ lowerValue ((point 2 split 4096 972+point 2 split 4096 973)/2)
    have hp : lowerPayment 972 = (130278498139:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 972+point 2 split 4096 973)/2 = (78834039:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((78834039:ℝ)/33751040)/ClassicalSixthBranch.v ((78834039:ℝ)/33751040) = (738827628739:ℝ)/373890788568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_972
  · change lowerPayment 973 ≤ lowerValue ((point 2 split 4096 973+point 2 split 4096 974)/2)
    have hp : lowerPayment 973 = (130390546352:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 973+point 2 split 4096 974)/2 = (394228457:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394228457:ℝ)/168755200)/ClassicalSixthBranch.v ((394228457:ℝ)/168755200) = (147750063013:ℝ)/74768556136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_973
  · change lowerPayment 974 ≤ lowerValue ((point 2 split 4096 974+point 2 split 4096 975)/2)
    have hp : lowerPayment 974 = (130502561668:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 974+point 2 split 4096 975)/2 = (394286719:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394286719:ℝ)/168755200)/ClassicalSixthBranch.v ((394286719:ℝ)/168755200) = (738673001391:ℝ)/373794772792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_974
  · change lowerPayment 975 ≤ lowerValue ((point 2 split 4096 975+point 2 split 4096 976)/2)
    have hp : lowerPayment 975 = (130614544117:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 975+point 2 split 4096 976)/2 = (394344981:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((394344981:ℝ)/168755200)/ClassicalSixthBranch.v ((394344981:ℝ)/168755200) = (738595687717:ℝ)/373746764904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_975
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_060
