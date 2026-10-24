import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints125
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_125 (j : Fin 16) : upperPayment (16*125+j.val) ≤
    upperValue ((point split endpoint 4096 (16*125+j.val)+point split endpoint 4096 (16*125+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2000 ≤ upperValue ((point split endpoint 4096 2000+point split endpoint 4096 2001)/2)
    have hp : upperPayment 2000 = (273978857821:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2000+point split endpoint 4096 2001)/2 = (626464127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626464127:ℝ)/168755200)*ClassicalSixthBranch.v ((626464127:ℝ)/168755200)/ClassicalSixthBranch.r = (114970362364817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2000
  · change upperPayment 2001 ≤ upperValue ((point split endpoint 4096 2001+point split endpoint 4096 2002)/2)
    have hp : upperPayment 2001 = (273880315018:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2001+point split endpoint 4096 2002)/2 = (626489277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626489277:ℝ)/168755200)*ClassicalSixthBranch.v ((626489277:ℝ)/168755200)/ClassicalSixthBranch.r = (114948395216025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2001
  · change upperPayment 2002 ≤ upperValue ((point split endpoint 4096 2002+point split endpoint 4096 2003)/2)
    have hp : upperPayment 2002 = (273781745988:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2002+point split endpoint 4096 2003)/2 = (626514427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626514427:ℝ)/168755200)*ClassicalSixthBranch.v ((626514427:ℝ)/168755200)/ClassicalSixthBranch.r = (114926430091305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2002
  · change upperPayment 2003 ≤ upperValue ((point split endpoint 4096 2003+point split endpoint 4096 2004)/2)
    have hp : upperPayment 2003 = (273683150728:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2003+point split endpoint 4096 2004)/2 = (626539577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626539577:ℝ)/168755200)*ClassicalSixthBranch.v ((626539577:ℝ)/168755200)/ClassicalSixthBranch.r = (114904466990657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2003
  · change upperPayment 2004 ≤ upperValue ((point split endpoint 4096 2004+point split endpoint 4096 2005)/2)
    have hp : upperPayment 2004 = (273584529231:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2004+point split endpoint 4096 2005)/2 = (626564727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626564727:ℝ)/168755200)*ClassicalSixthBranch.v ((626564727:ℝ)/168755200)/ClassicalSixthBranch.r = (114882505914081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2004
  · change upperPayment 2005 ≤ upperValue ((point split endpoint 4096 2005+point split endpoint 4096 2006)/2)
    have hp : upperPayment 2005 = (273485881493:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2005+point split endpoint 4096 2006)/2 = (626589877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626589877:ℝ)/168755200)*ClassicalSixthBranch.v ((626589877:ℝ)/168755200)/ClassicalSixthBranch.r = (114860546861577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2005
  · change upperPayment 2006 ≤ upperValue ((point split endpoint 4096 2006+point split endpoint 4096 2007)/2)
    have hp : upperPayment 2006 = (273387207508:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2006+point split endpoint 4096 2007)/2 = (626615027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626615027:ℝ)/168755200)*ClassicalSixthBranch.v ((626615027:ℝ)/168755200)/ClassicalSixthBranch.r = (114838589833145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2006
  · change upperPayment 2007 ≤ upperValue ((point split endpoint 4096 2007+point split endpoint 4096 2008)/2)
    have hp : upperPayment 2007 = (273288507272:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2007+point split endpoint 4096 2008)/2 = (626640177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626640177:ℝ)/168755200)*ClassicalSixthBranch.v ((626640177:ℝ)/168755200)/ClassicalSixthBranch.r = (114816634828785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2007
  · change upperPayment 2008 ≤ upperValue ((point split endpoint 4096 2008+point split endpoint 4096 2009)/2)
    have hp : upperPayment 2008 = (273189780778:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2008+point split endpoint 4096 2009)/2 = (626665327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626665327:ℝ)/168755200)*ClassicalSixthBranch.v ((626665327:ℝ)/168755200)/ClassicalSixthBranch.r = (114794681848497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2008
  · change upperPayment 2009 ≤ upperValue ((point split endpoint 4096 2009+point split endpoint 4096 2010)/2)
    have hp : upperPayment 2009 = (273091028022:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2009+point split endpoint 4096 2010)/2 = (626690477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626690477:ℝ)/168755200)*ClassicalSixthBranch.v ((626690477:ℝ)/168755200)/ClassicalSixthBranch.r = (114772730892281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2009
  · change upperPayment 2010 ≤ upperValue ((point split endpoint 4096 2010+point split endpoint 4096 2011)/2)
    have hp : upperPayment 2010 = (272992248999:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2010+point split endpoint 4096 2011)/2 = (626715627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626715627:ℝ)/168755200)*ClassicalSixthBranch.v ((626715627:ℝ)/168755200)/ClassicalSixthBranch.r = (114750781960137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2010
  · change upperPayment 2011 ≤ upperValue ((point split endpoint 4096 2011+point split endpoint 4096 2012)/2)
    have hp : upperPayment 2011 = (272893443703:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2011+point split endpoint 4096 2012)/2 = (626740777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626740777:ℝ)/168755200)*ClassicalSixthBranch.v ((626740777:ℝ)/168755200)/ClassicalSixthBranch.r = (114728835052065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2011
  · change upperPayment 2012 ≤ upperValue ((point split endpoint 4096 2012+point split endpoint 4096 2013)/2)
    have hp : upperPayment 2012 = (272794612130:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2012+point split endpoint 4096 2013)/2 = (626765927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626765927:ℝ)/168755200)*ClassicalSixthBranch.v ((626765927:ℝ)/168755200)/ClassicalSixthBranch.r = (114706890168065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2012
  · change upperPayment 2013 ≤ upperValue ((point split endpoint 4096 2013+point split endpoint 4096 2014)/2)
    have hp : upperPayment 2013 = (272695754273:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2013+point split endpoint 4096 2014)/2 = (626791077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626791077:ℝ)/168755200)*ClassicalSixthBranch.v ((626791077:ℝ)/168755200)/ClassicalSixthBranch.r = (114684947308137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2013
  · change upperPayment 2014 ≤ upperValue ((point split endpoint 4096 2014+point split endpoint 4096 2015)/2)
    have hp : upperPayment 2014 = (272596870129:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2014+point split endpoint 4096 2015)/2 = (626816227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626816227:ℝ)/168755200)*ClassicalSixthBranch.v ((626816227:ℝ)/168755200)/ClassicalSixthBranch.r = (114663006472281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2014
  · change upperPayment 2015 ≤ upperValue ((point split endpoint 4096 2015+point split endpoint 4096 2016)/2)
    have hp : upperPayment 2015 = (272497959691:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2015+point split endpoint 4096 2016)/2 = (626841377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626841377:ℝ)/168755200)*ClassicalSixthBranch.v ((626841377:ℝ)/168755200)/ClassicalSixthBranch.r = (114641067660497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2015
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_125
