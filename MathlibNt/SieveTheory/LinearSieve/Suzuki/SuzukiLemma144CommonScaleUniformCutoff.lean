import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIAbsorption
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIBracketGapQuantitative

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Uniform cutoffs for the common Lemma-14.4 scale

Claim 14.5 is chosen after the source small-parameter constant `C1`, whereas
Lemma 14.4 subsequently enlarges its error constant to

`C = max 3 (A * C145)`.

The old eventual Case-I and Case-II APIs accepted both `C` and `C145`, which
made their generated witnesses look as though they had to be paid by `C1`
after `C145` was known.  The two lemmas below expose the cancellations already
present in the production gap arguments.  Their eventual threshold is selected
before `C145` and `C`.
-/

/-- The common normalization used after Claim 14.5. -/
noncomputable def lemma144CommonScale (A C145 : ℝ) : ℝ :=
  max 3 (A * C145)

/-- Both elementary lower bounds supplied by the common normalization. -/
theorem lemma144CommonScale_bounds
    {A C145 : ℝ} :
    3 ≤ lemma144CommonScale A C145 ∧
      A * C145 ≤ lemma144CommonScale A C145 := by
  exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- In Case I every occurrence of the two late constants is through a scale
ratio.  Consequently one cutoff works for all `C145 ≥ 0` after imposing
`C = max 3 (A*C145)`.  `B/C` represents the normalized `Σ₁₁` coefficient and
`E` the already scale-free endpoint coefficient; in production these are the
only other summands next to `C145/C`.

The quantifier order is the point: the eventual `D` threshold precedes both
`C145` and `C`. -/
theorem eventually_caseISourceOrderCoefficient_commonScale_uniform
    {A B E d Δ : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    ∀ᶠ D : ℝ in atTop, ∀ (C145 C : ℝ),
      0 ≤ C145 → C = lemma144CommonScale A C145 →
      ∃ q : Lemma144StrictFactor,
        q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma D d) Δ) / 2 ∧
        caseISourceOrderCoefficient (C145 / C + B / C + E) D d ≤ 1 - q.ρ := by
  let U : ℝ := 1 / A + B / 3 + E
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have hgap := eventually_caseISourceOrderCoefficient_le_sameC_gap
    (A := U) hU hΔ0 hΔ1 hd
  filter_upwards [hgap, eventually_ge_atTop (Real.exp (Real.exp 1))]
    with D hgapD hD
  intro C145 C hC145 hCeq
  obtain ⟨q, hq, hqgap⟩ := hgapD
  refine ⟨q, hq, ?_⟩
  have hC3 : 3 ≤ C := by
    rw [hCeq]
    exact lemma144CommonScale_bounds.1
  have hCpos : 0 < C := by linarith
  have hAC : A * C145 ≤ C := by
    rw [hCeq]
    exact lemma144CommonScale_bounds.2
  have hratio145 : C145 / C ≤ 1 / A := by
    apply (div_le_iff₀ hCpos).2
    calc
      C145 = (A * C145) / A := by field_simp [ne_of_gt hA]
      _ ≤ C / A := div_le_div_of_nonneg_right hAC hA.le
      _ = (1 / A) * C := by ring
  have hratioB : B / C ≤ B / 3 := by
    exact div_le_div_of_nonneg_left hB (by norm_num) hC3
  have hnum : C145 / C + B / C + E ≤ U := by
    dsimp [U]
    linarith
  have hDpos : 0 < D := (Real.exp_pos (Real.exp 1)).trans_le hD
  have hlogD : Real.exp 1 ≤ Real.log D :=
    (Real.le_log_iff_exp_le hDpos).2 hD
  have hll : 0 < Real.log (Real.log D) := by
    apply Real.log_pos
    exact (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hlogD
  have hd0 : 0 < d := by
    have hden : 0 < 1 - Δ := sub_pos.mpr hΔ1
    have : 0 < 7 / (1 - Δ) := div_pos (by norm_num) hden
    linarith
  have hσ : 0 < sourceSigma D d := by
    unfold sourceSigma
    have hlog0 : 0 < Real.log D := (Real.exp_pos 1).trans_le hlogD
    have hinner : 1 < Real.log (27 * D) := by
      have h27D : Real.exp 1 < 27 * D := by
        have : 1 < D := by
          calc
            1 < Real.exp (Real.exp 1) := Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
            _ ≤ D := hD
        nlinarith [Real.exp_one_lt_d9]
      exact (Real.lt_log_iff_exp_lt (by positivity : 0 < 27 * D)).2 h27D
    exact mul_pos (Real.rpow_pos_of_pos hlog0 _) (Real.log_pos hinner)
  have hden : 0 < Real.log (Real.log D) * sourceSigma D d := mul_pos hll hσ
  have hcoef : caseISourceOrderCoefficient (C145 / C + B / C + E) D d ≤
      caseISourceOrderCoefficient U D d := by
    unfold caseISourceOrderCoefficient
    exact div_le_div_of_nonneg_right hnum hden.le
  exact hcoef.trans hqgap

/-- The Case-II endpoint inequality also depends only on `C145/C`.  This
explicit witness is uniform in the late Claim-14.5 constant and therefore can
be dominated by the already chosen source constant `C1`.

Unlike `exists_claim145_gap_constant_threshold`, the witness below depends on
`A,Δ` only, not on `C145` or `C`. -/
theorem exists_claim145_gap_constant_threshold_commonScale_uniform
    {A Δ : ℝ} (hA : 0 < A) (hΔ1 : Δ < 1) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ (C145 C D : ℝ),
      0 ≤ C145 → C = lemma144CommonScale A C145 → D0 ≤ D →
      C145 ≤ 27 * C * (1 - Δ) * Real.log D / 32 := by
  have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
  let a : ℝ := 32 / (27 * A * (1 - Δ))
  let X : ℝ := max 1 a
  refine ⟨Real.exp X,
    Real.one_lt_exp_iff.mpr (zero_lt_one.trans_le (le_max_left _ _)), ?_⟩
  intro C145 C D hC145 hCeq hD
  have hDpos : 0 < D := (Real.exp_pos X).trans_le hD
  have hlog : X ≤ Real.log D := (Real.le_log_iff_exp_le hDpos).2 hD
  have ha : a ≤ Real.log D := (le_max_right 1 a).trans hlog
  have hcoef : 0 < 27 * A * (1 - Δ) := by positivity
  have hunit : 32 ≤ (27 * A * (1 - Δ)) * Real.log D := by
    have := (div_le_iff₀ hcoef).mp (by simpa [a] using ha)
    nlinarith
  have hscale : A * C145 ≤ C := by
    rw [hCeq]
    exact lemma144CommonScale_bounds.2
  have hlog0 : 0 ≤ Real.log D := by
    have : 1 < D := by
      calc
        1 < Real.exp X := Real.one_lt_exp_iff.mpr
          (zero_lt_one.trans_le (le_max_left _ _))
        _ ≤ D := hD
    exact (Real.log_pos this).le
  have hm1 := mul_le_mul_of_nonneg_left hunit hC145
  have hm2 :
      (27 * A * (1 - Δ) * Real.log D) * C145 ≤
        (27 * C * (1 - Δ) * Real.log D) := by
    have hfac : 0 ≤ 27 * (1 - Δ) * Real.log D := by positivity
    have := mul_le_mul_of_nonneg_left hscale hfac
    nlinarith
  apply (le_div_iff₀ (show (0 : ℝ) < 32 by norm_num)).2
  nlinarith

/-- One outer cutoff simultaneously supplies the Case-I midpoint absorption
and the Case-II endpoint-gap inequality.  It is selected with `A,B,E,d,Δ`
fixed and before the late constants `C145,C`; this is the exact quantifier order
needed to choose `C1` first. -/
theorem exists_lemma144_caseI_caseII_commonScale_cutoff_uniform
    {A B E d Δ : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ (C145 C D : ℝ),
      0 ≤ C145 → C = lemma144CommonScale A C145 → D0 ≤ D →
      (∃ q : Lemma144StrictFactor,
        q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma D d) Δ) / 2 ∧
        caseISourceOrderCoefficient (C145 / C + B / C + E) D d ≤ 1 - q.ρ) ∧
      C145 ≤ 27 * C * (1 - Δ) * Real.log D / 32 := by
  have hI := eventually_caseISourceOrderCoefficient_commonScale_uniform
    hA hB hE hΔ0 hΔ1 hd
  obtain ⟨DI, hDI⟩ := eventually_atTop.1 hI
  obtain ⟨DII, hDII, hII⟩ :=
    exists_claim145_gap_constant_threshold_commonScale_uniform hA hΔ1
  refine ⟨max DI DII, hDII.trans_le (le_max_right _ _), ?_⟩
  intro C145 C D hC145 hCeq hD
  have hD_I : DI ≤ D := (le_max_left _ _).trans hD
  have hD_II : DII ≤ D := (le_max_right _ _).trans hD
  exact ⟨hDI D hD_I C145 C hC145 hCeq,
    hII C145 C D hC145 hCeq hD_II⟩


end MathlibNt.SieveTheory
