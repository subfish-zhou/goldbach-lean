import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiErrorEnvelopeCeilBridge

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


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
