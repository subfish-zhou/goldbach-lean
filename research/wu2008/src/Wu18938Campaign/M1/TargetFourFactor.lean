import Wu18938Campaign.M1.FourFactorSize

namespace Wu18938Campaign.M1

open Finset Wu2008DoubleSieve WuPaper.R2Mother
open scoped Classical

/-- The fixed parameters used by the Wu08 endpoint satisfy the additional
size condition needed to pay the classified four-factor subset. -/
theorem target_fourFactor_geometry :
    (1 / 18 : ℝ) ≤ 100 / 1327 ∧
    (100 / 1327 : ℝ) < 25 / 206 ∧
    3 * (100 / 1327 : ℝ) + 25 / 206 < 1 / 2 ∧
    3 * (100 / 1327 : ℝ) - 25 / 206 < 1 / 6 ∧
    (100 / 1327 : ℝ) ≤ 1 ∧
    3 * (25 / 206 : ℝ) - 2 * (100 / 1327) ≤ 1 / 2 := by
  norm_num

/-- Actual target-parameter specialization of the existing signed payment.
The other indices remain explicit; this is not the full mother inequality. -/
theorem target_residual_fourFactor_paid {N : ℕ} (hN : 1 ≤ N) :
    let κ₁ : ℝ := 100 / 1327
    let κ₂ : ℝ := 25 / 206
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    (quotientExcess N z w u V : ℝ) - quotientAssemblyGains N z w u v ≤
      2 * (N : ℝ) ^ (1 - κ₁) +
      ((∑ p ∈ range (N + 1) \ fourFactorIndices N z w u v V,
        (pointExcess N p z w u V - pointGains N p z w u v) : ℤ) : ℝ) -
      (4 * (N : ℝ) / w + 2 * (Real.sqrt N + 1)) -
      (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) := by
  exact source_residual_fourFactor_paid hN
    target_fourFactor_geometry.2.2.2.2.1 target_fourFactor_geometry.2.2.2.2.2

end Wu18938Campaign.M1

#check @Wu18938Campaign.M1.target_residual_fourFactor_paid
#print axioms Wu18938Campaign.M1.target_fourFactor_geometry
#print axioms Wu18938Campaign.M1.target_residual_fourFactor_paid
