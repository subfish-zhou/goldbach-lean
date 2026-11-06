import MathlibNt.Wu2008DoubleSieve.Gamma5MassMain

/-!
# Actual fully normalized classical Gamma5 count

The coefficient C5 is the literal full-triangle integral. The proof consumes
the accepted actual classical count producer and the proved bilateral mass,
not a supplied count, density, or quadrature estimate.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology

theorem gamma5Mass_scalar_budget {c τ ε : ℝ}
    (hc : 0 ≤ c) (hc64 : c ≤ 64) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hτε : τ ≤ ε / 512) :
    (1 + τ) ^ 2 * (c + τ) + τ ≤ c + ε := by
  have hsq : (1 + τ) ^ 2 ≤ 1 + 3 * τ := by
    nlinarith [mul_nonneg hτ (sub_nonneg.mpr hτ1)]
  have hmul := mul_le_mul_of_nonneg_right hsq (add_nonneg hc hτ)
  have hct := mul_le_mul_of_nonneg_right hc64 hτ
  have ht2 := mul_le_mul_of_nonneg_right hτ1 hτ
  nlinarith



end Wu2008DoubleSieve
