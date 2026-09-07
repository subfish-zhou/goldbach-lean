import MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticLogBounds
import MathlibNt.SieveTheory.LiLiuGoldbachG67G67Piecewise

open MeasureTheory Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section
namespace G67Centered

/-- Fixed analytic polynomial candidate. None of the approximation estimates
or the target coefficient is asserted by these definitions. -/
def a : ℝ := 4/53
def b : ℝ := 4/33
def c : ℝ := 3/11
def cutoff : ℝ := 1/2-2*a
def center : ℝ := (a+c)/2

def profilePolynomial (s : ℝ) : ℝ :=
  G9Analytic.logLower (37/16) +
    S3Correction.L ((((1/2-s)-a)/a)/(37/16)-1)

def shiftedLogPolynomial (t s : ℝ) : ℝ :=
  S3Correction.L ((s-t)/center-1)

def squareEarly (s : ℝ) : ℝ :=
  2*G9Analytic.logLower (center/a)+2*shiftedLogPolynomial a s

def squareLate (s : ℝ) : ℝ :=
  2*(G9Analytic.logLower (2*b/center)-G9Analytic.logUpper 2)-
    2*shiftedLogPolynomial b s

def rectangleEarly (s : ℝ) : ℝ :=
  G9Analytic.logLower (center^2/(a*b))+
    shiftedLogPolynomial b s+shiftedLogPolynomial a s

def rectangleMiddle (s : ℝ) : ℝ :=
  G9Analytic.logLower (b/a)+shiftedLogPolynomial a s-shiftedLogPolynomial b s

def rectangleLate (s : ℝ) : ℝ :=
  G9Analytic.logLower (b*c/center^2)-
    shiftedLogPolynomial c s-shiftedLogPolynomial b s

/-- Fixed geometric polynomial for 1/(s*(1/2-s)), centered at 1/4. -/
def reciprocalPolynomial (s : ℝ) : ℝ :=
  16*∑ k ∈ range 16, ((4*s-1)^2)^k

def densityPolynomial (w : ℝ → ℝ) (s : ℝ) : ℝ :=
  profilePolynomial s*w s*reciprocalPolynomial s

def polynomialIntegral : ℝ :=
  (1/2 : ℝ)*
    ((∫ s in (2*a)..(a+b), densityPolynomial squareEarly s)+
     (∫ s in (a+b)..(2*b), densityPolynomial squareLate s))+
    ((∫ s in (a+b)..(2*b), densityPolynomial rectangleEarly s)+
     (∫ s in (2*b)..(a+c), densityPolynomial rectangleMiddle s)+
     (∫ s in (a+c)..cutoff, densityPolynomial rectangleLate s))

/-- Candidate uniform density loss times the exact weighted interval length.
Its sufficiency must be proved separately, not inferred from this name. -/
def errorBudget : ℝ := (cutoff-2*a)/40000

end G67Centered
