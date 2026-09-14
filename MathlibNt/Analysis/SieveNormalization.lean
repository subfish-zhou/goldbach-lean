import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MathlibNt.Analysis.SieveNormalization

/-- Cancel the reciprocal exponential factors in an upper sieve main term. -/
theorem upper_exp_product {X V S L t c g : ℝ}
    (hX : 0 ≤ X) (ht : 0 ≤ t)
    (hV : V ≤ c * Real.exp (-g) * t * S / L) :
    X * (Real.exp g * t) * V ≤ c * t ^ 2 * S * X / L := by
  calc
    X * (Real.exp g * t) * V ≤
        X * (Real.exp g * t) * (c * Real.exp (-g) * t * S / L) :=
      mul_le_mul_of_nonneg_left hV (by positivity)
    _ = (Real.exp g * Real.exp (-g)) * (c * t ^ 2 * S * X / L) := by ring
    _ = c * t ^ 2 * S * X / L := by rw [← Real.exp_add]; simp

/-- Multiply a lower product estimate by the nonnegative lower density. -/
theorem lower_product {a t f X V M : ℝ}
    (hX : 0 ≤ X) (hf : 0 ≤ f) (hscale : a * t ≤ X * V)
    (hdensity : f * V ≤ M) : a * f * t ≤ X * M := by
  calc
    a * f * t = f * (a * t) := by ring
    _ ≤ f * (X * V) := mul_le_mul_of_nonneg_left hscale hf
    _ = X * (f * V) := by ring
    _ ≤ X * M := mul_le_mul_of_nonneg_left hdensity hX

end MathlibNt.Analysis.SieveNormalization
