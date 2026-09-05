import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12NatCeil
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma0Internal

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

/-- The exact `Σ₁₁` endpoint term displayed by the internal Lemma-8.7 bound. -/
noncomputable def caseISigma11EndpointRemainder
    (S : BoundingSieve) (N D z : ℕ) (K β s τ σ : ℝ) : ℝ :=
  suzukiVProduct S z *
    ((6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
      Real.log ((D : ℝ) ^ (1 / σ))) * (τ / s))

/-- The literal sum of all explicit Case-I side budgets currently exposed by
`Σ₀`, `Σ₁₁`, and `Σ₁₂`.  No absorption inequality is a field of this object. -/
noncomputable def caseIExplicitSideBudget
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D z : ℕ) (C C145 K β d Δ s τ σ : ℝ) : ℝ :=
  suzukiSigmaZeroClaim145Budget S H N D z d Δ σ K C145 +
    caseISigma11EndpointRemainder S N D z K β s τ σ +
    sigma12EndpointRemainder S H N D z C K d Δ s σ

/-- The source-order coefficient in Suzuki (14.23). -/
noncomputable def caseISourceOrderCoefficient (A D d : ℝ) : ℝ :=
  A / (Real.log (Real.log D) * sourceSigma D d)

/-- Bernoulli/weighted-AM--GM lower bound for the Claim-14.6 contraction gap. -/
theorem caseI_rpow_contraction_gap
    {Δ σ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hσ : 1 < σ) :
    (1 - Δ) / σ ≤ 1 - (1 - 1 / σ) ^ (1 - Δ) := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hbase0 : 0 ≤ 1 - 1 / σ := by
    rw [sub_nonneg, div_le_one hσ0]
    exact hσ.le
  have hamgm := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ 1 - Δ by linarith) hΔ0.le hbase0
    (show 0 ≤ (1 : ℝ) by norm_num) (show (1 - Δ) + Δ = 1 by ring)
  rw [Real.one_rpow, mul_one] at hamgm
  calc
    (1 - Δ) / σ = 1 - ((1 - Δ) * (1 - 1 / σ) + Δ * 1) := by
      field_simp [ne_of_gt hσ0]
      ring
    _ ≤ 1 - (1 - 1 / σ) ^ (1 - Δ) := sub_le_sub_left hamgm 1

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
    {A d Δ : ℝ} (hA : 0 ≤ A) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
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

/-- Budget-valued form of the scalar theorem.  The side term is the proved
source-order majorant, not an assumed absorption inequality. -/
theorem eventually_caseISourceOrderBudget_le_sameC_gap
    {A B d Δ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hd : 7 / (1 - Δ) < d) :
    ∀ᶠ D : ℝ in atTop,
      ∃ q : Lemma144StrictFactor,
        q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma D d) Δ) / 2 ∧
        caseISourceOrderCoefficient A D d * B ≤ (1 - q.ρ) * B := by
  filter_upwards [eventually_caseISourceOrderCoefficient_le_sameC_gap
      hA hΔ0 hΔ1 hd] with D hD
  obtain ⟨q, hq, hcoef⟩ := hD
  exact ⟨q, hq, mul_le_mul_of_nonneg_right hcoef hB⟩

/-- Case-I's three displayed remainder families have one Claim-14.5 constant
and two Lemma-8.7 endpoint constants `6 K²`.  For fixed positive `K`, their
combined source-order coefficient is therefore eventually inside the same-`C`
gap.  The theorem is scalar: it makes no assumption of the desired absorption
inequality. -/
theorem eventually_caseI_allExplicitRemainderCoefficient_le_sameC_gap
    {A145 K d Δ : ℝ} (hA145 : 0 ≤ A145) (hK : 0 < K)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hd : 7 / (1 - Δ) < d) :
    ∀ᶠ D : ℝ in atTop,
      ∃ q : Lemma144StrictFactor,
        q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma D d) Δ) / 2 ∧
        caseISourceOrderCoefficient (A145 + 12 * K ^ 2) D d ≤ 1 - q.ρ := by
  exact eventually_caseISourceOrderCoefficient_le_sameC_gap
    (by positivity) hΔ0 hΔ1 hd

/-- Earliest remaining non-scalar edge.  It says that the literal sum of the
three explicit API budgets has Suzuki's source order.  This is deliberately a
frozen proposition (not an axiom and not a premise of the scalar absorption
theorems): the reachable production cone contains no theorem simultaneously
normalising the Claim-14.5 `Σ₀` sum and the two Lemma-8.7 endpoints to the
inherited `errorEnvelope` budget. -/
def Lemma144CaseIExplicitRemaindersSourceOrder : Prop :=
  ∀ (S : BoundingSieve) (H : Section13HatLayers)
      (N : ℕ) (C C145 K β d Δ s τ : ℝ),
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ D : ℕ in atTop,
      let σ := sourceSigma (D : ℝ) d
      let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
      caseIExplicitSideBudget S H N D z C C145 K β d Δ s τ σ ≤
        caseISourceOrderCoefficient A (D : ℝ) d *
          sigma12InheritedBudget S H N D z C K d Δ s


end MathlibNt.SieveTheory
