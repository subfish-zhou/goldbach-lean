import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146IntegralClosure
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma133WeightedTail

open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-!
# Corrected-sign compact-head margin

For `κ = 1` we take `Δ₀ = 1` and
`θ = (Δ₀ - Δ) / 2 = (1 - Δ) / 2`.  Thus the positive exponent is
`Δ₀ - Δ`, not the reversed (and negative) printed sign `Δ - Δ₀`.
-/

/-- The corrected positive half-gap exponent for the `κ = 1` compact head. -/
noncomputable def compactHeadTheta (Δ : ℝ) : ℝ := (1 - Δ) / 2

/-- The coefficient at the fixed splitting point `M` corresponding to the
half-gap exponent. -/
noncomputable def compactHeadCoefficient (Δ M : ℝ) : ℝ :=
  (1 - 1 / M) ^ compactHeadTheta Δ

/-- The explicit coefficient margin between the half-gap coefficient and the
full source exponent `Δ₀ - Δ = 1 - Δ`. -/
noncomputable def compactHeadMargin (Δ M : ℝ) : ℝ :=
  compactHeadCoefficient Δ M - (1 - 1 / M) ^ (1 - Δ)

lemma corrected_deltaGap_pos {Δ : ℝ} (hΔ : Δ < 1) : 0 < (1 : ℝ) - Δ := by
  exact sub_pos.mpr hΔ

lemma compactHeadTheta_pos {Δ : ℝ} (hΔ : Δ < 1) :
    0 < compactHeadTheta Δ := by
  exact div_pos (corrected_deltaGap_pos hΔ) (by norm_num)

/-- The corrected sign gives a genuinely positive, completely explicit margin
at every fixed `M > 1`. -/
theorem compactHeadMargin_pos
    {Δ M : ℝ} (hΔ : Δ < 1) (hM : 1 < M) :
    0 < compactHeadMargin Δ M := by
  have hM0 : 0 < M := zero_lt_one.trans hM
  have hb0 : 0 < 1 - 1 / M :=
    sub_pos.mpr ((div_lt_one hM0).mpr hM)
  have hb1 : 1 - 1 / M < 1 := sub_lt_self _ (one_div_pos.mpr hM0)
  have hgap : 0 < (1 : ℝ) - Δ := corrected_deltaGap_pos hΔ
  have htheta_lt : compactHeadTheta Δ < 1 - Δ :=
    div_lt_self hgap (by norm_num)
  have hp := Real.rpow_lt_rpow_of_exponent_gt hb0 hb1 htheta_lt
  exact sub_pos.mpr hp




end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
