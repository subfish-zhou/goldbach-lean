import F1CrossCount

noncomputable section
open Real Set MeasureTheory FirstIntegralRecovery FirstCRationalPayment FreshRemainingFactors F1FactorCross
open scoped Interval
namespace WholeRetainedProduct

/-- The prescribed retained product, with neither factor truncated again. -/
def retained (u : ℝ) : ℝ :=
  (splitL (u-1)+kept (u-1))/u*(splitL (ratio u)+kept (ratio u))

/-- Exact on the whole real carrier; total division introduces no domain hypothesis. -/
theorem product_exact (u : ℝ) :
    log (u-1)/u*log (ratio u)=retained u+tails u := by
  unfold retained tails logTail
  ring

/-- The original domain version retains the original two logarithmic tails. -/
theorem integral_product_exact :
    (∫ u in (2:ℝ)..(927/200),log (u-1)/u*log (ratio u))=
      ∫ u in (2:ℝ)..(927/200),retained u+tails u := by
  exact intervalIntegral.integral_congr (fun u _ => product_exact u)

end WholeRetainedProduct
