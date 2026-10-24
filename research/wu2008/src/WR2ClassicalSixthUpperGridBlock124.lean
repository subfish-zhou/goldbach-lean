import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints124
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_124 (j : Fin 16) : upperPayment (16*124+j.val) ≤
    upperValue ((point split endpoint 4096 (16*124+j.val)+point split endpoint 4096 (16*124+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1984 ≤ upperValue ((point split endpoint 4096 1984+point split endpoint 4096 1985)/2)
    have hp : upperPayment 1984 = (275551980172:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1984+point split endpoint 4096 1985)/2 = (626061727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626061727:ℝ)/168755200)*ClassicalSixthBranch.v ((626061727:ℝ)/168755200)/ClassicalSixthBranch.r = (1119632155527:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1984
  · change upperPayment 1985 ≤ upperValue ((point split endpoint 4096 1985+point split endpoint 4096 1986)/2)
    have hp : upperPayment 1985 = (275453856281:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1985+point split endpoint 4096 1986)/2 = (626086877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626086877:ℝ)/168755200)*ClassicalSixthBranch.v ((626086877:ℝ)/168755200)/ClassicalSixthBranch.r = (115300112485337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1985
  · change upperPayment 1986 ≤ upperValue ((point split endpoint 4096 1986+point split endpoint 4096 1987)/2)
    have hp : upperPayment 1986 = (275355706246:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1986+point split endpoint 4096 1987)/2 = (626112027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626112027:ℝ)/168755200)*ClassicalSixthBranch.v ((626112027:ℝ)/168755200)/ClassicalSixthBranch.r = (115278114975465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1986
  · change upperPayment 1987 ≤ upperValue ((point split endpoint 4096 1987+point split endpoint 4096 1988)/2)
    have hp : upperPayment 1987 = (275257530062:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1987+point split endpoint 4096 1988)/2 = (626137177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626137177:ℝ)/168755200)*ClassicalSixthBranch.v ((626137177:ℝ)/168755200)/ClassicalSixthBranch.r = (115256119489665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1987
  · change upperPayment 1988 ≤ upperValue ((point split endpoint 4096 1988+point split endpoint 4096 1989)/2)
    have hp : upperPayment 1988 = (275159327725:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1988+point split endpoint 4096 1989)/2 = (626162327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626162327:ℝ)/168755200)*ClassicalSixthBranch.v ((626162327:ℝ)/168755200)/ClassicalSixthBranch.r = (115234126027937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1988
  · change upperPayment 1989 ≤ upperValue ((point split endpoint 4096 1989+point split endpoint 4096 1990)/2)
    have hp : upperPayment 1989 = (275061099229:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1989+point split endpoint 4096 1990)/2 = (626187477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626187477:ℝ)/168755200)*ClassicalSixthBranch.v ((626187477:ℝ)/168755200)/ClassicalSixthBranch.r = (115212134590281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1989
  · change upperPayment 1990 ≤ upperValue ((point split endpoint 4096 1990+point split endpoint 4096 1991)/2)
    have hp : upperPayment 1990 = (274962844570:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1990+point split endpoint 4096 1991)/2 = (626212627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626212627:ℝ)/168755200)*ClassicalSixthBranch.v ((626212627:ℝ)/168755200)/ClassicalSixthBranch.r = (86804932311:ℝ)/55297703936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1990
  · change upperPayment 1991 ≤ upperValue ((point split endpoint 4096 1991+point split endpoint 4096 1992)/2)
    have hp : upperPayment 1991 = (274864563741:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1991+point split endpoint 4096 1992)/2 = (626237777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626237777:ℝ)/168755200)*ClassicalSixthBranch.v ((626237777:ℝ)/168755200)/ClassicalSixthBranch.r = (115168157787185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1991
  · change upperPayment 1992 ≤ upperValue ((point split endpoint 4096 1992+point split endpoint 4096 1993)/2)
    have hp : upperPayment 1992 = (274766256738:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1992+point split endpoint 4096 1993)/2 = (626262927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626262927:ℝ)/168755200)*ClassicalSixthBranch.v ((626262927:ℝ)/168755200)/ClassicalSixthBranch.r = (115146172421745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1992
  · change upperPayment 1993 ≤ upperValue ((point split endpoint 4096 1993+point split endpoint 4096 1994)/2)
    have hp : upperPayment 1993 = (274667923555:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1993+point split endpoint 4096 1994)/2 = (626288077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626288077:ℝ)/168755200)*ClassicalSixthBranch.v ((626288077:ℝ)/168755200)/ClassicalSixthBranch.r = (115124189080377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1993
  · change upperPayment 1994 ≤ upperValue ((point split endpoint 4096 1994+point split endpoint 4096 1995)/2)
    have hp : upperPayment 1994 = (274569564188:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1994+point split endpoint 4096 1995)/2 = (626313227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626313227:ℝ)/168755200)*ClassicalSixthBranch.v ((626313227:ℝ)/168755200)/ClassicalSixthBranch.r = (115102207763081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1994
  · change upperPayment 1995 ≤ upperValue ((point split endpoint 4096 1995+point split endpoint 4096 1996)/2)
    have hp : upperPayment 1995 = (274471178631:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1995+point split endpoint 4096 1996)/2 = (626338377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626338377:ℝ)/168755200)*ClassicalSixthBranch.v ((626338377:ℝ)/168755200)/ClassicalSixthBranch.r = (115080228469857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1995
  · change upperPayment 1996 ≤ upperValue ((point split endpoint 4096 1996+point split endpoint 4096 1997)/2)
    have hp : upperPayment 1996 = (274372766880:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1996+point split endpoint 4096 1997)/2 = (626363527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626363527:ℝ)/168755200)*ClassicalSixthBranch.v ((626363527:ℝ)/168755200)/ClassicalSixthBranch.r = (115058251200705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1996
  · change upperPayment 1997 ≤ upperValue ((point split endpoint 4096 1997+point split endpoint 4096 1998)/2)
    have hp : upperPayment 1997 = (274274328928:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1997+point split endpoint 4096 1998)/2 = (626388677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626388677:ℝ)/168755200)*ClassicalSixthBranch.v ((626388677:ℝ)/168755200)/ClassicalSixthBranch.r = (115036275955625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1997
  · change upperPayment 1998 ≤ upperValue ((point split endpoint 4096 1998+point split endpoint 4096 1999)/2)
    have hp : upperPayment 1998 = (274175864771:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1998+point split endpoint 4096 1999)/2 = (626413827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626413827:ℝ)/168755200)*ClassicalSixthBranch.v ((626413827:ℝ)/168755200)/ClassicalSixthBranch.r = (115014302734617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1998
  · change upperPayment 1999 ≤ upperValue ((point split endpoint 4096 1999+point split endpoint 4096 2000)/2)
    have hp : upperPayment 1999 = (274077374404:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1999+point split endpoint 4096 2000)/2 = (626438977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((626438977:ℝ)/168755200)*ClassicalSixthBranch.v ((626438977:ℝ)/168755200)/ClassicalSixthBranch.r = (114992331537681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1999
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_124
