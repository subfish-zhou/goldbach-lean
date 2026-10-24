import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints125
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_125 (j : Fin 16) : lowerPayment (16*125+j.val) ≤
    lowerValue ((point 2 split 4096 (16*125+j.val)+point 2 split 4096 (16*125+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2000 ≤ lowerValue ((point 2 split 4096 2000+point 2 split 4096 2001)/2)
    have hp : lowerPayment 2000 = (232712998122:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2000+point 2 split 4096 2001)/2 = (454063531:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454063531:ℝ)/168755200)/ClassicalSixthBranch.v ((454063531:ℝ)/168755200) = (659349171867:ℝ)/324538679704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2000
  · change lowerPayment 2001 ≤ lowerValue ((point 2 split 4096 2001+point 2 split 4096 2002)/2)
    have hp : lowerPayment 2001 = (232804067384:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2001+point 2 split 4096 2002)/2 = (454121793:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454121793:ℝ)/168755200)/ClassicalSixthBranch.v ((454121793:ℝ)/168755200) = (659271858193:ℝ)/324490671816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2001
  · change lowerPayment 2002 ≤ lowerValue ((point 2 split 4096 2002+point 2 split 4096 2003)/2)
    have hp : lowerPayment 2002 = (232895126482:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2002+point 2 split 4096 2003)/2 = (90836011:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90836011:ℝ)/33751040)/ClassicalSixthBranch.v ((90836011:ℝ)/33751040) = (659194544519:ℝ)/324442663928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2002
  · change lowerPayment 2003 ≤ lowerValue ((point 2 split 4096 2003+point 2 split 4096 2004)/2)
    have hp : lowerPayment 2003 = (232986175433:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2003+point 2 split 4096 2004)/2 = (454238317:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454238317:ℝ)/168755200)/ClassicalSixthBranch.v ((454238317:ℝ)/168755200) = (131823446169:ℝ)/64878931208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2003
  · change lowerPayment 2004 ≤ lowerValue ((point 2 split 4096 2004+point 2 split 4096 2005)/2)
    have hp : lowerPayment 2004 = (233077214254:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2004+point 2 split 4096 2005)/2 = (454296579:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454296579:ℝ)/168755200)/ClassicalSixthBranch.v ((454296579:ℝ)/168755200) = (659039917171:ℝ)/324346648152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2004
  · change lowerPayment 2005 ≤ lowerValue ((point 2 split 4096 2005+point 2 split 4096 2006)/2)
    have hp : lowerPayment 2005 = (233168242961:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2005+point 2 split 4096 2006)/2 = (454354841:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454354841:ℝ)/168755200)/ClassicalSixthBranch.v ((454354841:ℝ)/168755200) = (658962603497:ℝ)/324298640264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2005
  · change lowerPayment 2006 ≤ lowerValue ((point 2 split 4096 2006+point 2 split 4096 2007)/2)
    have hp : lowerPayment 2006 = (233259261571:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2006+point 2 split 4096 2007)/2 = (454413103:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454413103:ℝ)/168755200)/ClassicalSixthBranch.v ((454413103:ℝ)/168755200) = (658885289823:ℝ)/324250632376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2006
  · change lowerPayment 2007 ≤ lowerValue ((point 2 split 4096 2007+point 2 split 4096 2008)/2)
    have hp : lowerPayment 2007 = (233350270101:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2007+point 2 split 4096 2008)/2 = (90894273:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90894273:ℝ)/33751040)/ClassicalSixthBranch.v ((90894273:ℝ)/33751040) = (658807976149:ℝ)/324202624488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2007
  · change lowerPayment 2008 ≤ lowerValue ((point 2 split 4096 2008+point 2 split 4096 2009)/2)
    have hp : lowerPayment 2008 = (233441268567:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2008+point 2 split 4096 2009)/2 = (4412909:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4412909:ℝ)/1638400)/ClassicalSixthBranch.v ((4412909:ℝ)/1638400) = (255817733:ℝ)/125885288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2008
  · change lowerPayment 2009 ≤ lowerValue ((point 2 split 4096 2009+point 2 split 4096 2010)/2)
    have hp : lowerPayment 2009 = (233532256986:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2009+point 2 split 4096 2010)/2 = (454587889:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454587889:ℝ)/168755200)/ClassicalSixthBranch.v ((454587889:ℝ)/168755200) = (658653348801:ℝ)/324106608712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2009
  · change lowerPayment 2010 ≤ lowerValue ((point 2 split 4096 2010+point 2 split 4096 2011)/2)
    have hp : lowerPayment 2010 = (233623235375:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2010+point 2 split 4096 2011)/2 = (454646151:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454646151:ℝ)/168755200)/ClassicalSixthBranch.v ((454646151:ℝ)/168755200) = (658576035127:ℝ)/324058600824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2010
  · change lowerPayment 2011 ≤ lowerValue ((point 2 split 4096 2011+point 2 split 4096 2012)/2)
    have hp : lowerPayment 2011 = (233714203750:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2011+point 2 split 4096 2012)/2 = (454704413:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454704413:ℝ)/168755200)/ClassicalSixthBranch.v ((454704413:ℝ)/168755200) = (658498721453:ℝ)/324010592936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2011
  · change lowerPayment 2012 ≤ lowerValue ((point 2 split 4096 2012+point 2 split 4096 2013)/2)
    have hp : lowerPayment 2012 = (233805162128:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2012+point 2 split 4096 2013)/2 = (18190507:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18190507:ℝ)/6750208)/ClassicalSixthBranch.v ((18190507:ℝ)/6750208) = (658421407779:ℝ)/323962585048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2012
  · change lowerPayment 2013 ≤ lowerValue ((point 2 split 4096 2013+point 2 split 4096 2014)/2)
    have hp : lowerPayment 2013 = (233896110526:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2013+point 2 split 4096 2014)/2 = (454820937:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454820937:ℝ)/168755200)/ClassicalSixthBranch.v ((454820937:ℝ)/168755200) = (131668818821:ℝ)/64782915432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2013
  · change lowerPayment 2014 ≤ lowerValue ((point 2 split 4096 2014+point 2 split 4096 2015)/2)
    have hp : lowerPayment 2014 = (233987048960:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2014+point 2 split 4096 2015)/2 = (454879199:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454879199:ℝ)/168755200)/ClassicalSixthBranch.v ((454879199:ℝ)/168755200) = (658266780431:ℝ)/323866569272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2014
  · change lowerPayment 2015 ≤ lowerValue ((point 2 split 4096 2015+point 2 split 4096 2016)/2)
    have hp : lowerPayment 2015 = (234077977446:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2015+point 2 split 4096 2016)/2 = (454937461:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454937461:ℝ)/168755200)/ClassicalSixthBranch.v ((454937461:ℝ)/168755200) = (658189466757:ℝ)/323818561384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2015
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_125
