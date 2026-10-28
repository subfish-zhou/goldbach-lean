import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointFromCaseI
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceFiniteAssembly

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The explicit `Σ₁₁` endpoint loss left by the Case-I estimate at the cubic
endpoint `β+1=3`. -/
noncomputable def caseIIEndpointSigma11
    (K : ℝ) (N : ℕ) (D σ : ℝ) : ℝ :=
  (6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2 /
    Real.log (D ^ (1 / σ))) * (3 / 3)

/-- The complete transported `q_D` contribution left by the Case-I estimate at
`β+1=3`. -/
noncomputable def caseIIEndpointQD
    (H : Section13HatLayers) (N : ℕ) (D d Δ σ C K : ℝ) : ℝ :=
  C * Real.exp (Real.sqrt K) * (Real.log D) ^ (-Δ) *
    ((1 / 3) * (∫ t in (3 : ℝ)..σ,
      qD H (ErrorSign.ofDepth N).opposite D d Δ t) +
      (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite D d Δ 3 /
        Real.log (D ^ (1 / σ))) * (3 / 3))


/-- At odd depth, the endpoint value of the finite source layer is
nonnegative on its exact parity domain. -/
theorem caseII_finiteSourceLayer_three_nonneg {N : ℕ} (hN : Odd N) :
    0 ≤ finiteSourceLayer 1 2 N 3 := by
  apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) N
  have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
  simp [KappaOneModel.parityDomain, hmod]
  norm_num

/-- The explicit `Σ₁₁` endpoint loss is nonnegative in the Case-II range. -/
theorem caseIIEndpointSigma11_nonneg {N D : ℕ} {K σ : ℝ}
    (hN : Odd N) (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ)) :
    0 ≤ caseIIEndpointSigma11 K N (D : ℝ) σ := by
  have hFprev : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2 := by
    apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) (N - 1)
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
    have hprev : (N - 1) % 2 = 0 := by omega
    simp [KappaOneModel.parityDomain, hprev]
  have hlogw : 0 < Real.log ((D : ℝ) ^ (1 / σ)) :=
    Real.log_pos (by linarith)
  unfold caseIIEndpointSigma11
  positivity

/-- The transported `q_D` endpoint contribution is nonnegative under the
Section-13 positivity contract and the Case-II endpoint hypotheses. -/
theorem caseIIEndpointQD_nonneg
    {H : Section13HatLayers} {N D : ℕ} {d Δ σ C K : ℝ}
    (hH : Section13HatContract H 2) (hD : 1 < (D : ℝ))
    (h3σ : 3 ≤ σ) (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ)) (hC : 0 ≤ C) :
    0 ≤ caseIIEndpointQD H N (D : ℝ) d Δ σ C K := by
  have hqnonneg : ∀ t ∈ Set.Icc (3 : ℝ) σ,
      0 ≤ qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t := by
    intro t ht
    rcases ht with ⟨ht3, _htσ⟩
    exact (qD_pos H (ErrorSign.ofDepth N).opposite hD (by linarith)
      (hH.positive (ErrorSign.ofDepth N).opposite (t - 1) (by linarith))).le
  have hint : 0 ≤ ∫ t in (3 : ℝ)..σ,
      qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t :=
    intervalIntegral.integral_nonneg h3σ hqnonneg
  have hq3 : 0 ≤ qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 :=
    (qD_pos H (ErrorSign.ofDepth N).opposite hD (by norm_num)
      (hH.positive (ErrorSign.ofDepth N).opposite (3 - 1) (by norm_num))).le
  have hlogw : 0 < Real.log ((D : ℝ) ^ (1 / σ)) :=
    Real.log_pos (by linarith)
  unfold caseIIEndpointQD
  positivity


/-- The Case-II logarithmic ratio follows from the two exact power coordinates. -/
theorem caseII_log_ratio_of_power_identities
    {D y z s : ℝ} (hD : Real.exp 1 ≤ D) (hs : 0 < s)
    (hy : y = D ^ (1 / 3 : ℝ)) (hz : z = D ^ (1 / s)) :
    Real.log z / Real.log y = 3 / s := by
  have hDpos : 0 < D := (Real.exp_pos 1).trans_le hD
  have hDgt1 : 1 < D := by
    have hexp : Real.exp 0 < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
    simpa using hexp.trans_le hD
  have hlogD : 0 < Real.log D := Real.log_pos hDgt1
  have hlogy : Real.log y = (1 / 3 : ℝ) * Real.log D := by
    rw [hy, Real.log_rpow hDpos]
  have hlogz : Real.log z = (1 / s) * Real.log D := by
    rw [hz, Real.log_rpow hDpos]
  rw [hlogz, hlogy]
  field_simp


end MathlibNt.SieveTheory
