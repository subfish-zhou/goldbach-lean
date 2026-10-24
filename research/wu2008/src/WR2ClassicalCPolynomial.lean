import WR2ClassicalLogPolynomialLower
import WR2ClassicalCWeighted

noncomputable section
namespace WuPaper.ClassicalCPolynomial
open Real Set MeasureTheory Wu08OriginalFirstSteps ClassicalPolynomialLower

def bPoly (y : ℝ) : ℝ := (1/4:ℝ)*y^2+(-1/6:ℝ)*y^3+(5/48:ℝ)*y^4+(-1/15:ℝ)*y^5+(13/576:ℝ)*y^6+(-5/672:ℝ)*y^7+(1/512:ℝ)*y^8

theorem bPoly_zero : bPoly 0 = 0 := by norm_num [bPoly]

theorem bPoly_deriv (y : ℝ) : HasDerivAt bPoly (logPoly y*reciprocal 2 y) y := by
  have h := (((((((((hasDerivAt_id y).pow 2).const_mul (1/4:ℝ)).add (((hasDerivAt_id y).pow 3).const_mul (-1/6:ℝ))).add (((hasDerivAt_id y).pow 4).const_mul (5/48:ℝ))).add (((hasDerivAt_id y).pow 5).const_mul (-1/15:ℝ))).add (((hasDerivAt_id y).pow 6).const_mul (13/576:ℝ))).add (((hasDerivAt_id y).pow 7).const_mul (-5/672:ℝ))).add (((hasDerivAt_id y).pow 8).const_mul (1/512:ℝ)))
  change HasDerivAt bPoly _ y at h
  apply h.congr_deriv
  dsimp [bPoly,logPoly,reciprocal]
  ring

def cPoly (y : ℝ) : ℝ := (1/36:ℝ)*y^3+(-1/48:ℝ)*y^4+(1/80:ℝ)*y^5+(-31/4320:ℝ)*y^6+(1621/544320:ℝ)*y^7+(-4759/4354560:ℝ)*y^8+(4553/13063680:ℝ)*y^9+(-403/5225472:ℝ)*y^10+(13/870912:ℝ)*y^11+(-1/497664:ℝ)*y^12

theorem cPoly_zero : cPoly 0 = 0 := by norm_num [cPoly]

theorem cPoly_deriv (y : ℝ) : HasDerivAt cPoly (bPoly y*reciprocal 3 y) y := by
  have h := ((((((((((((hasDerivAt_id y).pow 3).const_mul (1/36:ℝ)).add (((hasDerivAt_id y).pow 4).const_mul (-1/48:ℝ))).add (((hasDerivAt_id y).pow 5).const_mul (1/80:ℝ))).add (((hasDerivAt_id y).pow 6).const_mul (-31/4320:ℝ))).add (((hasDerivAt_id y).pow 7).const_mul (1621/544320:ℝ))).add (((hasDerivAt_id y).pow 8).const_mul (-4759/4354560:ℝ))).add (((hasDerivAt_id y).pow 9).const_mul (4553/13063680:ℝ))).add (((hasDerivAt_id y).pow 10).const_mul (-403/5225472:ℝ))).add (((hasDerivAt_id y).pow 11).const_mul (13/870912:ℝ))).add (((hasDerivAt_id y).pow 12).const_mul (-1/497664:ℝ)))
  change HasDerivAt cPoly _ y at h
  apply h.congr_deriv
  dsimp [bPoly,logPoly,reciprocal]
  ring

end WuPaper.ClassicalCPolynomial
#print axioms WuPaper.ClassicalCPolynomial.bPoly_deriv
#print axioms WuPaper.ClassicalCPolynomial.cPoly_deriv
