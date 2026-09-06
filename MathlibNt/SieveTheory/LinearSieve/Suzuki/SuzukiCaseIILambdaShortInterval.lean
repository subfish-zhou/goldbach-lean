import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointErrorAbsorption

open scoped Classical BigOperators Interval
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- On the odd Case-II initial interval, the cubic-endpoint lambda is bounded
by one explicit perturbation factor times the current lambda.  A factor one
would have the wrong direction in general. -/
theorem lambda_three_le_perturb_three_mul_lambda_caseII
    {H : Section13HatLayers} {D d s : ℝ}
    (hH : Section13HatContract H 2) (hD : 1 < D) (_hd : 0 ≤ d)
    (hs : 0 < s) (hs3 : s ≤ 3) :
    lambda H .plus D d 0 3 ≤
      perturbation D d 0 3 * lambda H .plus D d 0 s := by
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hbase : 1 ≤ 1 + s ^ d / Real.log D := by
    have hquot : 0 ≤ s ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg hs.le d) hlogD.le
    linarith
  have hpert_s : 1 ≤ perturbation D d 0 s := by
    rw [perturbation]
    norm_num
    exact Real.one_le_rpow hbase hs.le
  have hpert3 : 0 ≤ perturbation D d 0 3 := by
    rw [perturbation]
    positivity
  rw [lambda_eq_perturb_mul_weightedHat,
      lambda_eq_perturb_mul_weightedHat]
  have hinit3 := hH.initial_plus 3 (by norm_num) (by norm_num)
  norm_num at hinit3
  have hinits := hH.initial_plus s hs (by norm_num at hs3 ⊢; exact hs3)
  norm_num at hinits
  rw [hinit3, hinits]
  have hm := mul_le_mul_of_nonneg_left hpert_s hpert3
  simpa only [perturbation, zero_add, mul_one] using hm

/-- Correct Case-II integral absorption with an explicit short-interval lambda
ratio.  This replaces the generally false factor-one comparison
`lambda(3) ≤ lambda(s)`. -/
theorem caseII_integral_absorb_with_lambda_ratio
    {H : Section13HatLayers} {N : ℕ}
    {D d Δ σ s R : ℝ}
    (hs : 0 < s)
    (hcut : 0 ≤ (1 - 1 / σ) ^ (1 - Δ))
    (_hR : 0 ≤ R)
    (hiii :
      (∫ t in (3 : ℝ)..σ,
          qD H (ErrorSign.ofDepth N).opposite D d Δ t) ≤
        (1 - 1 / σ) ^ (1 - Δ) *
          lambda H (ErrorSign.ofDepth N) D d 0 3)
    (hLambda3 :
      lambda H (ErrorSign.ofDepth N) D d 0 3 ≤
        R * lambda H (ErrorSign.ofDepth N) D d 0 s) :
    (1 / s) * (∫ t in (3 : ℝ)..σ,
        qD H (ErrorSign.ofDepth N).opposite D d Δ t) ≤
      ((1 - 1 / σ) ^ (1 - Δ) * R) *
        errorEnvelope H N D d s := by
  let c : ℝ := (1 - 1 / σ) ^ (1 - Δ)
  let I : ℝ := ∫ t in (3 : ℝ)..σ,
    qD H (ErrorSign.ofDepth N).opposite D d Δ t
  have hscaledLambda : c * lambda H (ErrorSign.ofDepth N) D d 0 3 ≤
      c * (R * lambda H (ErrorSign.ofDepth N) D d 0 s) :=
    mul_le_mul_of_nonneg_left hLambda3 hcut
  have hI : I ≤ c * (R * lambda H (ErrorSign.ofDepth N) D d 0 s) :=
    hiii.trans hscaledLambda
  have hscaled := mul_le_mul_of_nonneg_left hI (one_div_pos.mpr hs).le
  calc
    (1 / s) * I ≤ (1 / s) *
        (c * (R * lambda H (ErrorSign.ofDepth N) D d 0 s)) := hscaled
    _ = (c * R) * errorEnvelope H N D d s := by
      rw [errorEnvelope_eq_lambda_div H hs]
      ring

end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
