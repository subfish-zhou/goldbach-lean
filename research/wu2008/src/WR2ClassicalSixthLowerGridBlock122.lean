import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints122
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_122 (j : Fin 16) : lowerPayment (16*122+j.val) ≤
    lowerValue ((point 2 split 4096 (16*122+j.val)+point 2 split 4096 (16*122+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1952 ≤ lowerValue ((point 2 split 4096 1952+point 2 split 4096 1953)/2)
    have hp : lowerPayment 1952 = (228329391905:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1952+point 2 split 4096 1953)/2 = (90253391:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90253391:ℝ)/33751040)/ClassicalSixthBranch.v ((90253391:ℝ)/33751040) = (663060228219:ℝ)/326843058328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1952
  · change lowerPayment 1953 ≤ lowerValue ((point 2 split 4096 1953+point 2 split 4096 1954)/2)
    have hp : lowerPayment 1953 = (228420968801:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1953+point 2 split 4096 1954)/2 = (451325217:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451325217:ℝ)/168755200)/ClassicalSixthBranch.v ((451325217:ℝ)/168755200) = (132596582909:ℝ)/65359010088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1953
  · change lowerPayment 1954 ≤ lowerValue ((point 2 split 4096 1954+point 2 split 4096 1955)/2)
    have hp : lowerPayment 1954 = (228512534724:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1954+point 2 split 4096 1955)/2 = (451383479:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451383479:ℝ)/168755200)/ClassicalSixthBranch.v ((451383479:ℝ)/168755200) = (662905600871:ℝ)/326747042552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1954
  · change lowerPayment 1955 ≤ lowerValue ((point 2 split 4096 1955+point 2 split 4096 1956)/2)
    have hp : lowerPayment 1955 = (228604089690:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1955+point 2 split 4096 1956)/2 = (451441741:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451441741:ℝ)/168755200)/ClassicalSixthBranch.v ((451441741:ℝ)/168755200) = (662828287197:ℝ)/326699034664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1955
  · change lowerPayment 1956 ≤ lowerValue ((point 2 split 4096 1956+point 2 split 4096 1957)/2)
    have hp : lowerPayment 1956 = (228695633717:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1956+point 2 split 4096 1957)/2 = (451500003:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451500003:ℝ)/168755200)/ClassicalSixthBranch.v ((451500003:ℝ)/168755200) = (662750973523:ℝ)/326651026776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1956
  · change lowerPayment 1957 ≤ lowerValue ((point 2 split 4096 1957+point 2 split 4096 1958)/2)
    have hp : lowerPayment 1957 = (228787166822:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1957+point 2 split 4096 1958)/2 = (90311653:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90311653:ℝ)/33751040)/ClassicalSixthBranch.v ((90311653:ℝ)/33751040) = (662673659849:ℝ)/326603018888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1957
  · change lowerPayment 1958 ≤ lowerValue ((point 2 split 4096 1958+point 2 split 4096 1959)/2)
    have hp : lowerPayment 1958 = (228878689021:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1958+point 2 split 4096 1959)/2 = (451616527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451616527:ℝ)/168755200)/ClassicalSixthBranch.v ((451616527:ℝ)/168755200) = (26503853847:ℝ)/13062200440 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1958
  · change lowerPayment 1959 ≤ lowerValue ((point 2 split 4096 1959+point 2 split 4096 1960)/2)
    have hp : lowerPayment 1959 = (228970200332:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1959+point 2 split 4096 1960)/2 = (451674789:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451674789:ℝ)/168755200)/ClassicalSixthBranch.v ((451674789:ℝ)/168755200) = (662519032501:ℝ)/326507003112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1959
  · change lowerPayment 1960 ≤ lowerValue ((point 2 split 4096 1960+point 2 split 4096 1961)/2)
    have hp : lowerPayment 1960 = (229061700772:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1960+point 2 split 4096 1961)/2 = (451733051:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451733051:ℝ)/168755200)/ClassicalSixthBranch.v ((451733051:ℝ)/168755200) = (662441718827:ℝ)/326458995224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1960
  · change lowerPayment 1961 ≤ lowerValue ((point 2 split 4096 1961+point 2 split 4096 1962)/2)
    have hp : lowerPayment 1961 = (229153190358:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1961+point 2 split 4096 1962)/2 = (451791313:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451791313:ℝ)/168755200)/ClassicalSixthBranch.v ((451791313:ℝ)/168755200) = (662364405153:ℝ)/326410987336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1961
  · change lowerPayment 1962 ≤ lowerValue ((point 2 split 4096 1962+point 2 split 4096 1963)/2)
    have hp : lowerPayment 1962 = (229244669106:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1962+point 2 split 4096 1963)/2 = (18073983:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18073983:ℝ)/6750208)/ClassicalSixthBranch.v ((18073983:ℝ)/6750208) = (662287091479:ℝ)/326362979448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1962
  · change lowerPayment 1963 ≤ lowerValue ((point 2 split 4096 1963+point 2 split 4096 1964)/2)
    have hp : lowerPayment 1963 = (229336137034:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1963+point 2 split 4096 1964)/2 = (451907837:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451907837:ℝ)/168755200)/ClassicalSixthBranch.v ((451907837:ℝ)/168755200) = (132441955561:ℝ)/65262994312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1963
  · change lowerPayment 1964 ≤ lowerValue ((point 2 split 4096 1964+point 2 split 4096 1965)/2)
    have hp : lowerPayment 1964 = (229427594158:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1964+point 2 split 4096 1965)/2 = (451966099:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((451966099:ℝ)/168755200)/ClassicalSixthBranch.v ((451966099:ℝ)/168755200) = (662132464131:ℝ)/326266963672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1964
  · change lowerPayment 1965 ≤ lowerValue ((point 2 split 4096 1965+point 2 split 4096 1966)/2)
    have hp : lowerPayment 1965 = (229519040496:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1965+point 2 split 4096 1966)/2 = (452024361:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452024361:ℝ)/168755200)/ClassicalSixthBranch.v ((452024361:ℝ)/168755200) = (662055150457:ℝ)/326218955784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1965
  · change lowerPayment 1966 ≤ lowerValue ((point 2 split 4096 1966+point 2 split 4096 1967)/2)
    have hp : lowerPayment 1966 = (229610476065:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1966+point 2 split 4096 1967)/2 = (452082623:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452082623:ℝ)/168755200)/ClassicalSixthBranch.v ((452082623:ℝ)/168755200) = (661977836783:ℝ)/326170947896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1966
  · change lowerPayment 1967 ≤ lowerValue ((point 2 split 4096 1967+point 2 split 4096 1968)/2)
    have hp : lowerPayment 1967 = (229701900881:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1967+point 2 split 4096 1968)/2 = (90428177:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90428177:ℝ)/33751040)/ClassicalSixthBranch.v ((90428177:ℝ)/33751040) = (661900523109:ℝ)/326122940008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1967
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_122
