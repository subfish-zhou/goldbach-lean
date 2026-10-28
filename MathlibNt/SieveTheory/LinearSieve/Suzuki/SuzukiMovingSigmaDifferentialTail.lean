import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaGeometryEventually

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000


/-- Express the delayed kernel as its perturbation-weighted DDE main term. -/
lemma qD_eq_dde_main
    {H : Section13HatLayers} {D d Δ t : ℝ} (sign : ErrorSign)
    (hlog : 0 < Real.log D) (ht : 1 < t) :
    qD H sign.opposite D d Δ t =
      (perturbation D d 0 t * (t * H.T sign.opposite (t - 1)) /
          (1 + t ^ d / Real.log D)) *
        ((t - 1) / t) ^ (1 - Δ) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have htm0 : 0 < t - 1 := sub_pos.mpr ht
  have hbase : 0 < 1 + t ^ d / Real.log D := by
    have : 0 ≤ t ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg ht0.le _) hlog.le
    linarith
  simp only [qD, Section13HatLayers.kappaHat, perturbation]
  norm_num [Real.rpow_one]
  rw [show t / (t - 1) = ((t - 1) / t)⁻¹ by rw [inv_div],
      Real.inv_rpow (div_pos htm0 ht0).le, ← Real.rpow_neg (div_pos htm0 ht0).le]
  rw [Real.rpow_sub_one hbase.ne']
  rw [show 1 - Δ = 1 + (-Δ) by ring,
      Real.rpow_add (div_pos htm0 ht0), Real.rpow_one]
  field_simp [hbase.ne', ne_of_gt ht0, ne_of_gt htm0]


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
