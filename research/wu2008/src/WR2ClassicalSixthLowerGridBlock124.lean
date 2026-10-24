import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints124
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_124 (j : Fin 16) : lowerPayment (16*124+j.val) ≤
    lowerValue ((point 2 split 4096 (16*124+j.val)+point 2 split 4096 (16*124+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1984 ≤ lowerValue ((point 2 split 4096 1984+point 2 split 4096 1985)/2)
    have hp : lowerPayment 1984 = (231254493998:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1984+point 2 split 4096 1985)/2 = (453131339:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453131339:ℝ)/168755200)/ClassicalSixthBranch.v ((453131339:ℝ)/168755200) = (660586190651:ℝ)/325306805912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1984
  · change lowerPayment 1985 ≤ lowerValue ((point 2 split 4096 1985+point 2 split 4096 1986)/2)
    have hp : lowerPayment 1985 = (231345728158:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1985+point 2 split 4096 1986)/2 = (453189601:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453189601:ℝ)/168755200)/ClassicalSixthBranch.v ((453189601:ℝ)/168755200) = (660508876977:ℝ)/325258798024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1985
  · change lowerPayment 1986 ≤ lowerValue ((point 2 split 4096 1986+point 2 split 4096 1987)/2)
    have hp : lowerPayment 1986 = (231436951886:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1986+point 2 split 4096 1987)/2 = (453247863:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453247863:ℝ)/168755200)/ClassicalSixthBranch.v ((453247863:ℝ)/168755200) = (660431563303:ℝ)/325210790136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1986
  · change lowerPayment 1987 ≤ lowerValue ((point 2 split 4096 1987+point 2 split 4096 1988)/2)
    have hp : lowerPayment 1987 = (231528165198:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1987+point 2 split 4096 1988)/2 = (18132245:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18132245:ℝ)/6750208)/ClassicalSixthBranch.v ((18132245:ℝ)/6750208) = (660354249629:ℝ)/325162782248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1987
  · change lowerPayment 1988 ≤ lowerValue ((point 2 split 4096 1988+point 2 split 4096 1989)/2)
    have hp : lowerPayment 1988 = (231619368113:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1988+point 2 split 4096 1989)/2 = (453364387:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453364387:ℝ)/168755200)/ClassicalSixthBranch.v ((453364387:ℝ)/168755200) = (132055387191:ℝ)/65022954872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1988
  · change lowerPayment 1989 ≤ lowerValue ((point 2 split 4096 1989+point 2 split 4096 1990)/2)
    have hp : lowerPayment 1989 = (231710560645:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1989+point 2 split 4096 1990)/2 = (453422649:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453422649:ℝ)/168755200)/ClassicalSixthBranch.v ((453422649:ℝ)/168755200) = (660199622281:ℝ)/325066766472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1989
  · change lowerPayment 1990 ≤ lowerValue ((point 2 split 4096 1990+point 2 split 4096 1991)/2)
    have hp : lowerPayment 1990 = (231801742813:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1990+point 2 split 4096 1991)/2 = (453480911:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453480911:ℝ)/168755200)/ClassicalSixthBranch.v ((453480911:ℝ)/168755200) = (660122308607:ℝ)/325018758584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1990
  · change lowerPayment 1991 ≤ lowerValue ((point 2 split 4096 1991+point 2 split 4096 1992)/2)
    have hp : lowerPayment 1991 = (231892914633:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1991+point 2 split 4096 1992)/2 = (453539173:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453539173:ℝ)/168755200)/ClassicalSixthBranch.v ((453539173:ℝ)/168755200) = (660044994933:ℝ)/324970750696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1991
  · change lowerPayment 1992 ≤ lowerValue ((point 2 split 4096 1992+point 2 split 4096 1993)/2)
    have hp : lowerPayment 1992 = (231984076122:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1992+point 2 split 4096 1993)/2 = (90719487:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90719487:ℝ)/33751040)/ClassicalSixthBranch.v ((90719487:ℝ)/33751040) = (659967681259:ℝ)/324922742808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1992
  · change lowerPayment 1993 ≤ lowerValue ((point 2 split 4096 1993+point 2 split 4096 1994)/2)
    have hp : lowerPayment 1993 = (232075227297:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1993+point 2 split 4096 1994)/2 = (453655697:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453655697:ℝ)/168755200)/ClassicalSixthBranch.v ((453655697:ℝ)/168755200) = (131978073517:ℝ)/64974946984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1993
  · change lowerPayment 1994 ≤ lowerValue ((point 2 split 4096 1994+point 2 split 4096 1995)/2)
    have hp : lowerPayment 1994 = (232166368173:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1994+point 2 split 4096 1995)/2 = (453713959:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453713959:ℝ)/168755200)/ClassicalSixthBranch.v ((453713959:ℝ)/168755200) = (659813053911:ℝ)/324826727032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1994
  · change lowerPayment 1995 ≤ lowerValue ((point 2 split 4096 1995+point 2 split 4096 1996)/2)
    have hp : lowerPayment 1995 = (232257498769:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1995+point 2 split 4096 1996)/2 = (453772221:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453772221:ℝ)/168755200)/ClassicalSixthBranch.v ((453772221:ℝ)/168755200) = (659735740237:ℝ)/324778719144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1995
  · change lowerPayment 1996 ≤ lowerValue ((point 2 split 4096 1996+point 2 split 4096 1997)/2)
    have hp : lowerPayment 1996 = (232348619101:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1996+point 2 split 4096 1997)/2 = (453830483:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453830483:ℝ)/168755200)/ClassicalSixthBranch.v ((453830483:ℝ)/168755200) = (659658426563:ℝ)/324730711256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1996
  · change lowerPayment 1997 ≤ lowerValue ((point 2 split 4096 1997+point 2 split 4096 1998)/2)
    have hp : lowerPayment 1997 = (232439729185:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1997+point 2 split 4096 1998)/2 = (90777749:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((90777749:ℝ)/33751040)/ClassicalSixthBranch.v ((90777749:ℝ)/33751040) = (659581112889:ℝ)/324682703368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1997
  · change lowerPayment 1998 ≤ lowerValue ((point 2 split 4096 1998+point 2 split 4096 1999)/2)
    have hp : lowerPayment 1998 = (232530829039:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1998+point 2 split 4096 1999)/2 = (453947007:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((453947007:ℝ)/168755200)/ClassicalSixthBranch.v ((453947007:ℝ)/168755200) = (131900759843:ℝ)/64926939096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1998
  · change lowerPayment 1999 ≤ lowerValue ((point 2 split 4096 1999+point 2 split 4096 2000)/2)
    have hp : lowerPayment 1999 = (232621918679:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1999+point 2 split 4096 2000)/2 = (454005269:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((454005269:ℝ)/168755200)/ClassicalSixthBranch.v ((454005269:ℝ)/168755200) = (659426485541:ℝ)/324586687592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1999
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_124
