import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints123
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_123 (j : Fin 16) : upperPayment (16*123+j.val) ≤
    upperValue ((point split endpoint 4096 (16*123+j.val)+point split endpoint 4096 (16*123+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1968 ≤ upperValue ((point split endpoint 4096 1968+point split endpoint 4096 1969)/2)
    have hp : upperPayment 1968 = (277118411137:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1968+point split endpoint 4096 1969)/2 = (625659327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625659327:ℝ)/168755200)*ClassicalSixthBranch.v ((625659327:ℝ)/168755200)/ClassicalSixthBranch.r = (115674379836177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1968
  · change upperPayment 1969 ≤ upperValue ((point split endpoint 4096 1969+point split endpoint 4096 1970)/2)
    have hp : upperPayment 1969 = (277020704840:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1969+point split endpoint 4096 1970)/2 = (625684477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625684477:ℝ)/168755200)*ClassicalSixthBranch.v ((625684477:ℝ)/168755200)/ClassicalSixthBranch.r = (115652347917081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1969
  · change upperPayment 1970 ≤ upperValue ((point split endpoint 4096 1970+point split endpoint 4096 1971)/2)
    have hp : upperPayment 1970 = (276922972483:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1970+point split endpoint 4096 1971)/2 = (625709627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625709627:ℝ)/168755200)*ClassicalSixthBranch.v ((625709627:ℝ)/168755200)/ClassicalSixthBranch.r = (115630318022057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1970
  · change upperPayment 1971 ≤ upperValue ((point split endpoint 4096 1971+point split endpoint 4096 1972)/2)
    have hp : upperPayment 1971 = (276825214058:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1971+point split endpoint 4096 1972)/2 = (625734777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625734777:ℝ)/168755200)*ClassicalSixthBranch.v ((625734777:ℝ)/168755200)/ClassicalSixthBranch.r = (115608290151105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1971
  · change upperPayment 1972 ≤ upperValue ((point split endpoint 4096 1972+point split endpoint 4096 1973)/2)
    have hp : upperPayment 1972 = (276727429563:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1972+point split endpoint 4096 1973)/2 = (625759927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625759927:ℝ)/168755200)*ClassicalSixthBranch.v ((625759927:ℝ)/168755200)/ClassicalSixthBranch.r = (115586264304225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1972
  · change upperPayment 1973 ≤ upperValue ((point split endpoint 4096 1973+point split endpoint 4096 1974)/2)
    have hp : upperPayment 1973 = (276629618990:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1973+point split endpoint 4096 1974)/2 = (625785077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625785077:ℝ)/168755200)*ClassicalSixthBranch.v ((625785077:ℝ)/168755200)/ClassicalSixthBranch.r = (115564240481417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1973
  · change upperPayment 1974 ≤ upperValue ((point split endpoint 4096 1974+point split endpoint 4096 1975)/2)
    have hp : upperPayment 1974 = (276531782336:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1974+point split endpoint 4096 1975)/2 = (625810227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625810227:ℝ)/168755200)*ClassicalSixthBranch.v ((625810227:ℝ)/168755200)/ClassicalSixthBranch.r = (115542218682681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1974
  · change upperPayment 1975 ≤ upperValue ((point split endpoint 4096 1975+point split endpoint 4096 1976)/2)
    have hp : upperPayment 1975 = (276433919596:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1975+point split endpoint 4096 1976)/2 = (625835377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625835377:ℝ)/168755200)*ClassicalSixthBranch.v ((625835377:ℝ)/168755200)/ClassicalSixthBranch.r = (115520198908017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1975
  · change upperPayment 1976 ≤ upperValue ((point split endpoint 4096 1976+point split endpoint 4096 1977)/2)
    have hp : upperPayment 1976 = (276336030763:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1976+point split endpoint 4096 1977)/2 = (625860527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625860527:ℝ)/168755200)*ClassicalSixthBranch.v ((625860527:ℝ)/168755200)/ClassicalSixthBranch.r = (115498181157425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1976
  · change upperPayment 1977 ≤ upperValue ((point split endpoint 4096 1977+point split endpoint 4096 1978)/2)
    have hp : upperPayment 1977 = (276238115833:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1977+point split endpoint 4096 1978)/2 = (625885677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625885677:ℝ)/168755200)*ClassicalSixthBranch.v ((625885677:ℝ)/168755200)/ClassicalSixthBranch.r = (115476165430905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1977
  · change upperPayment 1978 ≤ upperValue ((point split endpoint 4096 1978+point split endpoint 4096 1979)/2)
    have hp : upperPayment 1978 = (276140174800:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1978+point split endpoint 4096 1979)/2 = (625910827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625910827:ℝ)/168755200)*ClassicalSixthBranch.v ((625910827:ℝ)/168755200)/ClassicalSixthBranch.r = (115454151728457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1978
  · change upperPayment 1979 ≤ upperValue ((point split endpoint 4096 1979+point split endpoint 4096 1980)/2)
    have hp : upperPayment 1979 = (276042207661:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1979+point split endpoint 4096 1980)/2 = (625935977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625935977:ℝ)/168755200)*ClassicalSixthBranch.v ((625935977:ℝ)/168755200)/ClassicalSixthBranch.r = (115432140050081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1979
  · change upperPayment 1980 ≤ upperValue ((point split endpoint 4096 1980+point split endpoint 4096 1981)/2)
    have hp : upperPayment 1980 = (275944214409:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1980+point split endpoint 4096 1981)/2 = (625961127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625961127:ℝ)/168755200)*ClassicalSixthBranch.v ((625961127:ℝ)/168755200)/ClassicalSixthBranch.r = (115410130395777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1980
  · change upperPayment 1981 ≤ upperValue ((point split endpoint 4096 1981+point split endpoint 4096 1982)/2)
    have hp : upperPayment 1981 = (275846195039:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1981+point split endpoint 4096 1982)/2 = (625986277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((625986277:ℝ)/168755200)*ClassicalSixthBranch.v ((625986277:ℝ)/168755200)/ClassicalSixthBranch.r = (115388122765545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1981
  · change upperPayment 1982 ≤ upperValue ((point split endpoint 4096 1982+point split endpoint 4096 1983)/2)
    have hp : upperPayment 1982 = (275748149546:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1982+point split endpoint 4096 1983)/2 = (626011427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626011427:ℝ)/168755200)*ClassicalSixthBranch.v ((626011427:ℝ)/168755200)/ClassicalSixthBranch.r = (115366117159385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1982
  · change upperPayment 1983 ≤ upperValue ((point split endpoint 4096 1983+point split endpoint 4096 1984)/2)
    have hp : upperPayment 1983 = (275650077926:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1983+point split endpoint 4096 1984)/2 = (626036577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626036577:ℝ)/168755200)*ClassicalSixthBranch.v ((626036577:ℝ)/168755200)/ClassicalSixthBranch.r = (115344113577297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1983
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_123
