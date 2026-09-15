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

/-- Direct Lemma-13.3 witness with the corrected positive exponent.  This is
the strict compactness input behind the quantitative margin. -/
theorem compactHead_weightedTail_strict
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {Δ M : ℝ} (hΔ : Δ < 1) (hM : 3 ≤ M) :
    (∫ t in (3 : ℝ)..M,
        ((t - 1) / t) ^ compactHeadTheta Δ * hatTailIntegrand H sign t) <
      weightedHat H sign 3 := by
  apply lemma13_3_weightedTail_strict_closedRange hH sign
  · exact (compactHeadTheta_pos hΔ).le
  · cases sign <;> norm_num [ErrorSign.epsilon]
  · exact hM

/-- Explicit positive-margin form of the fixed compact head.  The established
DDE/FTC compact-head estimate actually has the stronger coefficient
`(1 - 1/M)^(1-Δ)`.  Rewriting that coefficient as
`compactHeadCoefficient - compactHeadMargin` exposes a fixed positive amount
which is available for absorbing the moving tail.

The threshold is fixed after `M`; no fixed-endpoint theorem is diagonalized at
a moving source cutoff. -/
theorem eventually_compactHead_le_coefficient_sub_margin
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {d Δ M : ℝ}
    (hd : 0 ≤ d) (hΔ : Δ < 1) (hM : 3 ≤ M) :
    0 < compactHeadMargin Δ M ∧
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      (∫ t in (3 : ℝ)..M, qD H sign.opposite D d Δ t) ≤
        (compactHeadCoefficient Δ M - compactHeadMargin Δ M) *
          lambda H sign D d 0 3 := by
  have hmargin : 0 < compactHeadMargin Δ M :=
    compactHeadMargin_pos hΔ (by linarith)
  refine ⟨hmargin, ?_⟩
  have hsource : 2 + sign.epsilon ≤ (3 : ℝ) := by
    cases sign <;> norm_num [ErrorSign.epsilon]
  obtain ⟨D₀, hD₀, hhead⟩ :=
    claim14_6_iii_for_sufficiently_large_D_no_extra_premise
      hH sign hd hΔ hsource hM
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD
  have hstrict := hhead D hD
  have hcoeff :
      compactHeadCoefficient Δ M - compactHeadMargin Δ M =
        (1 - 1 / M) ^ (1 - Δ) := by
    simp only [compactHeadMargin]
    ring
  rw [hcoeff]
  exact hstrict.le


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
