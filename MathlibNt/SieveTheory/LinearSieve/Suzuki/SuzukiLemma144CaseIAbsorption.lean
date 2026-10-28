import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12NatCeil

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Lemma 14.4, Case I: the same-constant scalar absorption edge

The three displayed side terms in the current Case-I API are the Claim-14.5
`Σ₀` budget, the Lemma-8.7 endpoint in `Σ₁₁`, and the Lemma-8.7 endpoint in
`Σ₁₂`.  Suzuki's (14.23) reduces their sum to a fixed multiple of

`B / (log (log D) * sourceSigma D d)`,

where `B` is the inherited same-`C` budget.  The theorem below proves, rather
than assumes, that every such fixed source-order side term is eventually paid
for by the canonical midpoint gap from Claim 14.6(iii).
-/


/-- The source-order coefficient in Suzuki (14.23). -/
noncomputable def caseISourceOrderCoefficient (A D d : ℝ) : ℝ :=
  A / (Real.log (Real.log D) * sourceSigma D d)

/-- Bernoulli/weighted-AM--GM lower bound for the Claim-14.6 contraction gap. -/
theorem caseI_rpow_contraction_gap
    {Δ σ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hσ : 1 < σ) :
    (1 - Δ) / σ ≤ 1 - (1 - 1 / σ) ^ (1 - Δ) := by
  exact MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne.rpow_contraction_gap
    hΔ0 hΔ1 hσ

/-- The canonical midpoint strict factor leaves at least half of the elementary
Claim-14.6 gap. -/
theorem caseI_midpoint_gap_lower
    {Δ σ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hσ : 1 < σ) :
    ∃ q : Lemma144StrictFactor,
      q.ρ = (1 + sigma12ContractionMultiplier σ Δ) / 2 ∧
      (1 - Δ) / (2 * σ) ≤ 1 - q.ρ := by
  obtain ⟨q, hq, _⟩ := exists_sigma12_sameC_strictFactor hσ hΔ1
  refine ⟨q, hq, ?_⟩
  have hgap := caseI_rpow_contraction_gap hΔ0 hΔ1 hσ
  rw [hq]
  unfold sigma12ContractionMultiplier
  calc
    (1 - Δ) / (2 * σ) = ((1 - Δ) / σ) / 2 := by ring
    _ ≤ (1 - (1 - 1 / σ) ^ (1 - Δ)) / 2 :=
      div_le_div_of_nonneg_right hgap (by norm_num)
    _ = 1 - (1 + (1 - 1 / σ) ^ (1 - Δ)) / 2 := by ring

/-- Every fixed source-order side coefficient is eventually absorbed by the
same-`C` midpoint gap.  This is the complete scalar step in (14.23); its proof
uses the literal `sourceSigma` and the growth of `log (log D)`. -/
theorem eventually_caseISourceOrderCoefficient_le_sameC_gap
    {A d Δ : ℝ} (_hA : 0 ≤ A) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    ∀ᶠ D : ℝ in atTop,
      ∃ q : Lemma144StrictFactor,
        q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma D d) Δ) / 2 ∧
        caseISourceOrderCoefficient A D d ≤ 1 - q.ρ := by
  have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
  have hd0 : 0 < d := by
    have : 0 < 7 / (1 - Δ) := by positivity
    linarith
  have hloglog : Tendsto (fun D : ℝ => Real.log (Real.log D)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  let L : ℝ := max 1 (2 * A / (1 - Δ))
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 1)),
      hloglog.eventually_ge_atTop L] with D hD hll
  have hDpos : 0 < D := (Real.exp_pos (Real.exp 1)).trans_le hD
  have hlogDlower : Real.exp 1 ≤ Real.log D :=
    (Real.le_log_iff_exp_le hDpos).2 hD
  have hlogD1 : 1 ≤ Real.log D :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hlogDlower
  have hlog27D : Real.log (27 * D) = Real.log 27 + Real.log D := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hinner : Real.exp 1 < Real.log (27 * D) := by
    rw [hlog27D]
    have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hinnerpos : 0 < Real.log (27 * D) := (Real.exp_pos 1).trans hinner
  have hll27 : 1 < Real.log (Real.log (27 * D)) := by
    exact (Real.lt_log_iff_exp_lt hinnerpos).2 hinner
  have hfirst : 1 ≤ (Real.log D) ^ (1 / d) :=
    Real.one_le_rpow hlogD1 (one_div_nonneg.mpr hd0.le)
  have hσ : 1 < sourceSigma D d := by
    rw [sourceSigma]
    have hfirst0 : 0 < (Real.log D) ^ (1 / d) := by positivity
    calc
      1 ≤ (Real.log D) ^ (1 / d) := hfirst
      _ < (Real.log D) ^ (1 / d) * Real.log (Real.log (27 * D)) := by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hll27 hfirst0
  obtain ⟨q, hq, hqgap⟩ := caseI_midpoint_gap_lower hΔ0 hΔ1 hσ
  refine ⟨q, hq, ?_⟩
  have hll1 : 1 ≤ Real.log (Real.log D) := (le_max_left 1 _).trans hll
  have hllpos : 0 < Real.log (Real.log D) := zero_lt_one.trans_le hll1
  have hσpos : 0 < sourceSigma D d := zero_lt_one.trans hσ
  have hL : 2 * A / (1 - Δ) ≤ Real.log (Real.log D) :=
    (le_max_right 1 _).trans hll
  have hAover : A / Real.log (Real.log D) ≤ (1 - Δ) / 2 := by
    rw [div_le_iff₀ hllpos]
    have := mul_le_mul_of_nonneg_right hL (show 0 ≤ (1 - Δ) / 2 by positivity)
    field_simp [ne_of_gt hβ] at this ⊢
    nlinarith
  unfold caseISourceOrderCoefficient
  have hdivide := div_le_div_of_nonneg_right hAover hσpos.le
  calc
    A / (Real.log (Real.log D) * sourceSigma D d) =
        (A / Real.log (Real.log D)) / sourceSigma D d := by ring
    _ ≤ ((1 - Δ) / 2) / sourceSigma D d := hdivide
    _ = (1 - Δ) / (2 * sourceSigma D d) := by ring
    _ ≤ 1 - q.ρ := hqgap


end MathlibNt.SieveTheory
