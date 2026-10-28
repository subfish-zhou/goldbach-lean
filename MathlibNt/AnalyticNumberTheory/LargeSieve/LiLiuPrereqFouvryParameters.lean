import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Admissible C.2 factor levels, including the endpoint

In the interior these are the exponents printed in Fouvry (1987), p. 620.
When the printed S exponent is negative, set S = 1 and transfer its exponent
to R, keeping the original level exactly. This is only a parameter lemma:
it does not assert any distribution estimate or a dyadic decomposition.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

noncomputable section

def c2SExponent (ν ε : ℝ) : ℝ := max 0 ((1 - 10 * ν) / 9 - ε / 2)

def c2RExponent (ν ε : ℝ) : ℝ := (5 - 5 * ν) / 9 - ε - c2SExponent ν ε

theorem c2_exponent_bounds {ν ε : ℝ} (hε : 0 ≤ ε)
    (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10) :
    0 ≤ c2RExponent ν ε ∧ 0 ≤ c2SExponent ν ε ∧
      c2RExponent ν ε + c2SExponent ν ε = (5 - 5 * ν) / 9 - ε ∧
      2 * c2RExponent ν ε + c2SExponent ν ε ≤ 1 - 3 * ε / 2 ∧
      5 * ν / 4 + 7 * c2RExponent ν ε / 4 + 2 * c2SExponent ν ε ≤
        1 - 3 * ε / 2 := by
  unfold c2RExponent c2SExponent
  by_cases hs : 0 ≤ (1 - 10 * ν) / 9 - ε / 2
  · rw [max_eq_right hs]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rw [max_eq_left (by linarith : (1 - 10 * ν) / 9 - ε / 2 ≤ 0)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem c2SExponent_eq_zero_near_endpoint {ν ε : ℝ}
    (h : (1 - 10 * ν) / 9 ≤ ε / 2) :
    c2SExponent ν ε = 0 := by
  exact max_eq_left (sub_nonpos.mpr h)


end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
