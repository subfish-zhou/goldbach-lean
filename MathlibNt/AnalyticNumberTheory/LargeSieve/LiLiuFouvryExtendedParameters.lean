import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectGlobalParameters

/-!
# A small upper-end extension of the original Fouvry parameters

The definitions `c2RExponent` and `c2SExponent` are imported unchanged.
Only scalar parameter inequalities are extended; no distribution theorem,
coefficient estimate, G9 boundary reduction, or residue claim is made here.
The old range is discharged by the existing producers whenever applicable.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The new parameter range still bounds epsilon and nu by 1/9. -/
theorem c2_extended_parameter_caps {ν ε : ℝ}
    (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10 + ε / 10) :
    ε ≤ 1 / 9 ∧ ν ≤ 1 / 9 := by
  constructor <;> linarith

/-- Above the old endpoint the original S exponent vanishes. -/
theorem c2_extended_S_eq_zero {ν ε : ℝ}
    (hε : 0 < ε) (hν : 1 / 10 < ν) : c2SExponent ν ε = 0 := by
  apply c2SExponent_eq_zero_near_endpoint
  linarith

/-- Nonnegative exponents, the original level identity, and both original
strong inequalities hold on the slightly extended range. -/
theorem c2_extended_exponent_bounds {ν ε : ℝ} (hε : 0 < ε)
    (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10 + ε / 10) :
    0 ≤ c2RExponent ν ε ∧ 0 ≤ c2SExponent ν ε ∧
      c2RExponent ν ε + c2SExponent ν ε = (5 - 5 * ν) / 9 - ε ∧
      2 * c2RExponent ν ε + c2SExponent ν ε ≤ 1 - 3 * ε / 2 ∧
      5 * ν / 4 + 7 * c2RExponent ν ε / 4 + 2 * c2SExponent ν ε ≤
        1 - 3 * ε / 2 := by
  by_cases hold : ν ≤ 1 / 10
  · exact c2_exponent_bounds hε.le hεν hold
  · have hs := c2_extended_S_eq_zero hε (lt_of_not_ge hold)
    obtain ⟨hεcap, hνcap⟩ := c2_extended_parameter_caps hεν hν
    unfold c2RExponent
    rw [hs]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The original secondary margin survives the upper-end extension. -/
theorem c2_extended_secondary_exponent_margin {ν ε : ℝ}
    (hε : 0 < ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10 + ε / 10) :
    ν + 3 * c2RExponent ν ε / 4 + 3 * c2SExponent ν ε / 2 - 1 / 2 ≤
      -(3 * ε / 4) := by
  by_cases hold : ν ≤ 1 / 10
  · exact c2_direct_secondary_exponent_margin hε.le hεν hold
  · have hs := c2_extended_S_eq_zero hε (lt_of_not_ge hold)
    obtain ⟨hεcap, hνcap⟩ := c2_extended_parameter_caps hεν hν
    unfold c2RExponent
    rw [hs]
    linarith

/-- All three normalized terms admit the same original loss allowance. -/
theorem c2_extended_normalized_margins {ν ε L : ℝ}
    (hε : 0 < ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10 + ε / 10)
    (hL : L ≤ ε / 4) :
    c2RExponent ν ε + c2SExponent ν ε / 2 - 1 / 2 + L ≤ -(ε / 2) ∧
    5 * ν / 4 + 7 * c2RExponent ν ε / 4 + 2 * c2SExponent ν ε - 1 + L ≤
      -(ε / 2) ∧
    ν + 3 * c2RExponent ν ε / 4 + 3 * c2SExponent ν ε / 2 - 1 / 2 + L ≤
      -(ε / 2) := by
  by_cases hold : ν ≤ 1 / 10
  · exact c2_direct_normalized_margins hε.le hεν hold hL
  · obtain ⟨_, _, _, hfirst, hsecond⟩ := c2_extended_exponent_bounds hε hεν hν
    have hthird := c2_extended_secondary_exponent_margin hε hεν hν
    refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The short coordinate times S remains below the square-root level. -/
theorem c2_extended_short_add_S_le_half {ν ε : ℝ}
    (hε : 0 < ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10 + ε / 10) :
    ν + c2SExponent ν ε ≤ 1 / 2 := by
  obtain ⟨hεcap, hνcap⟩ := c2_extended_parameter_caps hεν hν
  unfold c2SExponent
  have hmax : max 0 ((1 - 10 * ν) / 9 - ε / 2) ≤ 1 / 2 - ν :=
    max_le (by linarith) (by linarith)
  linarith

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
