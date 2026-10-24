import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints123
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_123 (j : Fin 16) : lowerPayment (16*123+j.val) ≤
    lowerValue ((point 2 split 4096 (16*123+j.val)+point 2 split 4096 (16*123+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1968 ≤ lowerValue ((point 2 split 4096 1968+point 2 split 4096 1969)/2)
    have hp : lowerPayment 1968 = (229793314961:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1968+point 2 split 4096 1969)/2 = (452199147:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452199147:ℝ)/168755200)/ClassicalSixthBranch.v ((452199147:ℝ)/168755200) = (132364641887:ℝ)/65214986424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1968
  · change lowerPayment 1969 ≤ lowerValue ((point 2 split 4096 1969+point 2 split 4096 1970)/2)
    have hp : lowerPayment 1969 = (229884718323:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1969+point 2 split 4096 1970)/2 = (452257409:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452257409:ℝ)/168755200)/ClassicalSixthBranch.v ((452257409:ℝ)/168755200) = (661745895761:ℝ)/326026924232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1969
  · change lowerPayment 1970 ≤ lowerValue ((point 2 split 4096 1970+point 2 split 4096 1971)/2)
    have hp : lowerPayment 1970 = (229976110983:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1970+point 2 split 4096 1971)/2 = (452315671:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452315671:ℝ)/168755200)/ClassicalSixthBranch.v ((452315671:ℝ)/168755200) = (661668582087:ℝ)/325978916344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1970
  · change lowerPayment 1971 ≤ lowerValue ((point 2 split 4096 1971+point 2 split 4096 1972)/2)
    have hp : lowerPayment 1971 = (230067492958:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1971+point 2 split 4096 1972)/2 = (452373933:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452373933:ℝ)/168755200)/ClassicalSixthBranch.v ((452373933:ℝ)/168755200) = (661591268413:ℝ)/325930908456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1971
  · change lowerPayment 1972 ≤ lowerValue ((point 2 split 4096 1972+point 2 split 4096 1973)/2)
    have hp : lowerPayment 1972 = (230158864266:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1972+point 2 split 4096 1973)/2 = (90486439:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90486439:ℝ)/33751040)/ClassicalSixthBranch.v ((90486439:ℝ)/33751040) = (661513954739:ℝ)/325882900568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1972
  · change lowerPayment 1973 ≤ lowerValue ((point 2 split 4096 1973+point 2 split 4096 1974)/2)
    have hp : lowerPayment 1973 = (230250224922:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1973+point 2 split 4096 1974)/2 = (452490457:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452490457:ℝ)/168755200)/ClassicalSixthBranch.v ((452490457:ℝ)/168755200) = (132287328213:ℝ)/65166978536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1973
  · change lowerPayment 1974 ≤ lowerValue ((point 2 split 4096 1974+point 2 split 4096 1975)/2)
    have hp : lowerPayment 1974 = (230341574944:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1974+point 2 split 4096 1975)/2 = (452548719:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452548719:ℝ)/168755200)/ClassicalSixthBranch.v ((452548719:ℝ)/168755200) = (661359327391:ℝ)/325786884792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1974
  · change lowerPayment 1975 ≤ lowerValue ((point 2 split 4096 1975+point 2 split 4096 1976)/2)
    have hp : lowerPayment 1975 = (230432914349:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1975+point 2 split 4096 1976)/2 = (452606981:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452606981:ℝ)/168755200)/ClassicalSixthBranch.v ((452606981:ℝ)/168755200) = (661282013717:ℝ)/325738876904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1975
  · change lowerPayment 1976 ≤ lowerValue ((point 2 split 4096 1976+point 2 split 4096 1977)/2)
    have hp : lowerPayment 1976 = (230524243153:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1976+point 2 split 4096 1977)/2 = (452665243:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452665243:ℝ)/168755200)/ClassicalSixthBranch.v ((452665243:ℝ)/168755200) = (661204700043:ℝ)/325690869016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1976
  · change lowerPayment 1977 ≤ lowerValue ((point 2 split 4096 1977+point 2 split 4096 1978)/2)
    have hp : lowerPayment 1977 = (230615561374:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1977+point 2 split 4096 1978)/2 = (90544701:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90544701:ℝ)/33751040)/ClassicalSixthBranch.v ((90544701:ℝ)/33751040) = (661127386369:ℝ)/325642861128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1977
  · change lowerPayment 1978 ≤ lowerValue ((point 2 split 4096 1978+point 2 split 4096 1979)/2)
    have hp : lowerPayment 1978 = (230706869028:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1978+point 2 split 4096 1979)/2 = (452781767:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452781767:ℝ)/168755200)/ClassicalSixthBranch.v ((452781767:ℝ)/168755200) = (132210014539:ℝ)/65118970648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1978
  · change lowerPayment 1979 ≤ lowerValue ((point 2 split 4096 1979+point 2 split 4096 1980)/2)
    have hp : lowerPayment 1979 = (230798166133:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1979+point 2 split 4096 1980)/2 = (452840029:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452840029:ℝ)/168755200)/ClassicalSixthBranch.v ((452840029:ℝ)/168755200) = (660972759021:ℝ)/325546845352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1979
  · change lowerPayment 1980 ≤ lowerValue ((point 2 split 4096 1980+point 2 split 4096 1981)/2)
    have hp : lowerPayment 1980 = (230889452704:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1980+point 2 split 4096 1981)/2 = (452898291:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452898291:ℝ)/168755200)/ClassicalSixthBranch.v ((452898291:ℝ)/168755200) = (660895445347:ℝ)/325498837464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1980
  · change lowerPayment 1981 ≤ lowerValue ((point 2 split 4096 1981+point 2 split 4096 1982)/2)
    have hp : lowerPayment 1981 = (230980728760:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1981+point 2 split 4096 1982)/2 = (452956553:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((452956553:ℝ)/168755200)/ClassicalSixthBranch.v ((452956553:ℝ)/168755200) = (660818131673:ℝ)/325450829576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1981
  · change lowerPayment 1982 ≤ lowerValue ((point 2 split 4096 1982+point 2 split 4096 1983)/2)
    have hp : lowerPayment 1982 = (231071994316:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1982+point 2 split 4096 1983)/2 = (90602963:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90602963:ℝ)/33751040)/ClassicalSixthBranch.v ((90602963:ℝ)/33751040) = (660740817999:ℝ)/325402821688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1982
  · change lowerPayment 1983 ≤ lowerValue ((point 2 split 4096 1983+point 2 split 4096 1984)/2)
    have hp : lowerPayment 1983 = (231163249390:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1983+point 2 split 4096 1984)/2 = (453073077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453073077:ℝ)/168755200)/ClassicalSixthBranch.v ((453073077:ℝ)/168755200) = (26426540173:ℝ)/13014192552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1983
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_123
