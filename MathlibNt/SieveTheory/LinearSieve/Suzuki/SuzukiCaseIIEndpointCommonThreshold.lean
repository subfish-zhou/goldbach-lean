import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaPowerDecay
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISharpPositiveEndpointCoefficients

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- Beyond an explicit fixed threshold, Suzuki's moving source cutoff is at least one. -/
theorem exists_sourceSigma_one_threshold
    (d : ℝ) (hd : 0 < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D → 1 ≤ sourceSigma D d := by
  let D0 : ℝ := Real.exp (Real.exp 1)
  have hD0 : 1 < D0 := by
    dsimp [D0]
    exact Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
  refine ⟨D0, hD0, ?_⟩
  intro D hD
  have hDpos : 0 < D := (Real.exp_pos (Real.exp 1)).trans_le hD
  have hx : Real.exp 1 ≤ Real.log D := by
    exact (Real.le_log_iff_exp_le hDpos).2 hD
  have hxone : 1 ≤ Real.log D := by
    exact (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).le.trans hx
  have hpow : 1 ≤ (Real.log D) ^ (1 / d) := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hxone (by positivity : 0 ≤ 1 / d)
  have hlog27D : Real.log (27 * D) = Real.log 27 + Real.log D := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hinner : Real.exp 1 ≤ Real.log (27 * D) := by
    rw [hlog27D]
    have hlog27 : 0 ≤ Real.log (27 : ℝ) := (Real.log_pos (by norm_num)).le
    linarith
  have hll : 1 ≤ Real.log (Real.log (27 * D)) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hinner
  unfold sourceSigma
  exact one_le_mul_of_one_le_of_one_le hpow hll

/-- The four positive Case-II endpoint coefficients admit one unconditional
large-`D` threshold after substituting Suzuki's source cutoff.  The coefficients
`a₀`, `a₁`, and `aq₀` are fixed by `N,K,C,d,Δ`; all of the moving `D` dependence
is displayed in the four summands. -/
theorem exists_caseII_endpoint_common_threshold
    (N : ℕ) (K C d Δ : ℝ)
    (hF0 : 0 ≤ finiteSourceLayer 1 2 N 3)
    (hF1 : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      caseIISharpPositiveEndpointRelativeCoeff
          N D d Δ (sourceSigma D d) C K ≤
        4 * ((1 - Δ) / (32 * sourceSigma D d)) := by
  have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
  have hd0 : 0 < d := by
    have : 0 < 7 / (1 - Δ) := by positivity
    linarith
  have ha0 : 0 ≤ caseIIAlgebraicEndpointCoeffA0 N K := by
    unfold caseIIAlgebraicEndpointCoeffA0
    positivity
  have ha1 : 0 ≤ caseIIAlgebraicEndpointCoeffA1 N K := by
    unfold caseIIAlgebraicEndpointCoeffA1
    positivity
  have haq0 : 0 ≤ caseIIQDRelativeEndpointCoeffA0 d Δ C K := by
    unfold caseIIQDRelativeEndpointCoeffA0
    positivity
  have hbase : 0 ≤ 27 * K := by positivity
  obtain ⟨Dσ, hDσ, hsigma⟩ := exists_sourceSigma_one_threshold d hd0
  obtain ⟨D0a, hD0a, ha⟩ :=
    exists_sourceSigma_sq_positive_delta_decay_threshold
      Δ d (caseIIAlgebraicEndpointCoeffA0 N K) hΔ0 hΔ1 hd ha0
  obtain ⟨D1a, hD1a, h1⟩ :=
    exists_sourceSigma_sq_positive_delta_decay_threshold
      Δ d (caseIIAlgebraicEndpointCoeffA1 N K) hΔ0 hΔ1 hd ha1
  obtain ⟨Dqa, hDqa, hq⟩ :=
    exists_sourceSigma_sq_one_div_log_decay_threshold
      Δ d (caseIIQDRelativeEndpointCoeffA0 d Δ C K) hΔ0 hΔ1 hd haq0
  obtain ⟨Dba, hDba, hb⟩ :=
    exists_sourceSigma_sq_positive_delta_decay_threshold
      Δ d (27 * K) hΔ0 hΔ1 hd hbase
  let D0 : ℝ := max (max Dσ D0a) (max D1a (max Dqa Dba))
  have hD0 : 1 < D0 := hDσ.trans_le <|
    (le_max_left Dσ D0a).trans (le_max_left (max Dσ D0a) _)
  refine ⟨D0, hD0, ?_⟩
  intro D hD
  have hDσD : Dσ ≤ D :=
    (le_max_left Dσ D0a).trans ((le_max_left (max Dσ D0a) _).trans hD)
  have hD0aD : D0a ≤ D :=
    (le_max_right Dσ D0a).trans ((le_max_left (max Dσ D0a) _).trans hD)
  have hD1aD : D1a ≤ D :=
    (le_max_left D1a (max Dqa Dba)).trans
      ((le_max_right (max Dσ D0a) _).trans hD)
  have hDqaD : Dqa ≤ D :=
    (le_max_left Dqa Dba).trans
      ((le_max_right D1a (max Dqa Dba)).trans
        ((le_max_right (max Dσ D0a) _).trans hD))
  have hDbaD : Dba ≤ D :=
    (le_max_right Dqa Dba).trans
      ((le_max_right D1a (max Dqa Dba)).trans
        ((le_max_right (max Dσ D0a) _).trans hD))
  let σ : ℝ := sourceSigma D d
  let T : ℝ := (1 - Δ) / (32 * σ)
  have hσone : 1 ≤ σ := by simpa [σ] using hsigma D hDσD
  have hσ0 : 0 ≤ σ := zero_le_one.trans hσone
  have hDone : 1 < D := hDσ.trans_le hDσD
  have hlogD : 0 < Real.log D := Real.log_pos hDone
  have hp : 0 ≤ (Real.log D) ^ (Δ - 1) := Real.rpow_nonneg hlogD.le _
  have ha0raw :
      caseIIAlgebraicEndpointCoeffA0 N K * (Real.log D) ^ (Δ - 1) ≤ T := by
    have hscale :
        caseIIAlgebraicEndpointCoeffA0 N K * (Real.log D) ^ (Δ - 1) ≤
          caseIIAlgebraicEndpointCoeffA0 N K * σ * (Real.log D) ^ (Δ - 1) := by
      have := mul_le_mul_of_nonneg_left hσone ha0
      nlinarith [mul_nonneg ha0 hp]
    exact hscale.trans (by simpa [σ, T] using ha D hD0aD)
  have ha1raw :
      σ * caseIIAlgebraicEndpointCoeffA1 N K * (Real.log D) ^ (Δ - 1) ≤ T := by
    have := h1 D hD1aD
    simpa [σ, T, mul_comm] using this
  have hqraw :
      σ * caseIIQDRelativeEndpointCoeffA0 d Δ C K / Real.log D ≤ T := by
    have := hq D hDqaD
    simpa [σ, T, mul_comm] using this
  have hbraw : 27 * K * (Real.log D) ^ (Δ - 1) ≤ T := by
    have hscale :
        27 * K * (Real.log D) ^ (Δ - 1) ≤
          (27 * K) * σ * (Real.log D) ^ (Δ - 1) := by
      have := mul_le_mul_of_nonneg_left hσone hbase
      nlinarith [mul_nonneg hbase hp]
    exact hscale.trans (by simpa [σ, T] using hb D hDbaD)
  rw [caseIISharpPositiveEndpointRelativeCoeff_eq]
  change _ ≤ 4 * T
  linarith


end MathlibNt.SieveTheory
