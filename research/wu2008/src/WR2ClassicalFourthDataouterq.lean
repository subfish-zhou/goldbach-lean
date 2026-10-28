import WR2ClassicalFourthDataB
import WR2ClassicalFourthDataD
namespace WuPaper.ClassicalFourthData
/-- Exact ceiling of the outer integrand, with the original finite-table support. -/
def outerq (i : ℕ) : ℕ :=
  if i ≤ 10540 then
    let numerator := 2654*4000^2*(1000000000000000+B i+(if 8000 ≤ i then D (i-8000) else 0))
    let denominator := (12000+i)*(5308000-200*(12000+i))
    (numerator+denominator-1)/denominator
  else 0
end WuPaper.ClassicalFourthData
