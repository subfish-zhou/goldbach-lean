import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146ShortInterval
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaGeometryEventually

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The minimal missing Proposition 13.1 input.  It is pointwise and upstream
of integration: on each of the two source ranges it says that the perturbation
slope is absorbed by the delayed/current DDE ratio. -/
def MovingDDEAsymptoticCertificate
    (H : Section13HatLayers) (sign : ErrorSign) (d M : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    M ≤ sourceSigma D d ∧
    (∀ t, M ≤ t → t ≤ (Real.log D) ^ (1 / d) →
      weightedHat H sign t * perturbationSlope D d 0 t ≤
        t * H.T sign.opposite (t - 1) *
          ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D))) ∧
    (∀ t, (Real.log D) ^ (1 / d) < t → t ≤ sourceSigma D d →
      weightedHat H sign t * perturbationSlope D d 0 t ≤
        t * H.T sign.opposite (t - 1) *
          ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)))

private noncomputable def lambdaNegDeriv
    (H : Section13HatLayers) (sign : ErrorSign) (D d t : ℝ) : ℝ :=
  perturbation D d 0 t *
    (t * H.T sign.opposite (t - 1) -
      weightedHat H sign t * perturbationSlope D d 0 t)

private lemma hasDerivAt_lambdaNeg
    {H : Section13HatLayers} {β D d t : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hlog : 0 < Real.log D) (ht0 : 0 < t)
    (ht : β + sign.epsilon < t) :
    HasDerivAt (-lambda H sign D d 0)
      (lambdaNegDeriv H sign D d t) t := by
  have h := (hasDerivAt_lambda_of_contract (d := d) hH sign hlog
    (show 0 < t + 0 by linarith) ht).neg
  have heq : lambdaNegDeriv H sign D d t =
      -(perturbation D d 0 t *
        (weightedHat H sign t * perturbationSlope D d 0 t -
          t * H.T sign.opposite (t - 1))) := by
    unfold lambdaNegDeriv
    ring
  rw [heq]
  simpa only [Pi.neg_apply, perturbationSlope] using h

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


private lemma qD_le_lambdaNegDeriv_mul_weight
    {H : Section13HatLayers} {β D d Δ t : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hlog : 0 < Real.log D) (ht : 1 < t)
    (hasymp : weightedHat H sign t * perturbationSlope D d 0 t ≤
      t * H.T sign.opposite (t - 1) *
        ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D))) :
    qD H sign.opposite D d Δ t ≤
      lambdaNegDeriv H sign D d t * ((t - 1) / t) ^ (1 - Δ) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hlog0 : 0 < Real.log D := hlog
  let z : ℝ := t ^ d / Real.log D
  have hz0 : 0 ≤ z := div_nonneg (Real.rpow_nonneg ht0.le _) hlog.le
  have hb : 0 < 1 + z := by linarith
  have hmain : t * H.T sign.opposite (t - 1) / (1 + z) ≤
      t * H.T sign.opposite (t - 1) -
        weightedHat H sign t * perturbationSlope D d 0 t := by
    have hT0 : 0 ≤ t * H.T sign.opposite (t - 1) :=
      (mul_pos ht0 (hH.positive sign.opposite (t - 1) (sub_pos.mpr ht))).le
    dsimp [z] at hasymp ⊢
    calc
      t * H.T sign.opposite (t - 1) / (1 + t ^ d / Real.log D) =
          t * H.T sign.opposite (t - 1) -
            t * H.T sign.opposite (t - 1) *
              ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)) := by
            field_simp [hb.ne']
            ring
      _ ≤ t * H.T sign.opposite (t - 1) -
            weightedHat H sign t * perturbationSlope D d 0 t := sub_le_sub_left hasymp _
  have hp0 : 0 ≤ perturbation D d 0 t := by
    rw [perturbation]
    simpa [z] using Real.rpow_nonneg hb.le t
  have hw0 : 0 ≤ ((t - 1) / t) ^ (1 - Δ) := Real.rpow_nonneg (div_pos (sub_pos.mpr ht) ht0).le _
  rw [qD_eq_dde_main sign hlog ht]
  dsimp [lambdaNegDeriv]
  apply mul_le_mul_of_nonneg_right _ hw0
  convert mul_le_mul_of_nonneg_left hmain hp0 using 1; ring

private lemma continuousOn_lambdaNegDeriv
    {H : Section13HatLayers} {β D d a b : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hlog : 0 < Real.log D) (ha : β + sign.epsilon < a) :
    ContinuousOn (lambdaNegDeriv H sign D d) (Icc a b) := by
  have he : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
  have ha0 : 0 < a := by linarith [hH.beta_gt_one]
  have hp : ContinuousOn (perturbation D d 0) (Icc a b) := by
    intro t ht
    exact (hasDerivAt_perturbation (d := d) hlog (by simpa using ha0.trans_le ht.1)).continuousAt.continuousWithinAt
  have hT : ContinuousOn (fun t => t * H.T sign.opposite (t - 1)) (Icc a b) :=
    continuousOn_id.mul ((hH.continuous sign.opposite).comp
      (continuousOn_id.sub continuousOn_const) (by
        intro t ht
        have : 1 < t := by linarith [hH.beta_gt_one, ha, ht.1]
        exact sub_pos.mpr this))
  have hw : ContinuousOn (weightedHat H sign) (Icc a b) :=
    (continuousOn_id.pow 2).mul ((hH.continuous sign).mono (by
      intro t ht
      exact ha0.trans_le ht.1))
  have hs : ContinuousOn (perturbationSlope D d 0) (Icc a b) := by
    intro t ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    have hden : 0 < 1 + (t + 0) ^ d / Real.log D := by
      have : 0 ≤ (t + 0) ^ d / Real.log D :=
        div_nonneg (Real.rpow_nonneg (by linarith) _) hlog.le
      linarith
    unfold perturbationSlope
    fun_prop (disch := aesop)
  exact hp.mul (hT.sub (hw.mul hs))

private lemma continuousOn_qD_tail
    {H : Section13HatLayers} {β D d Δ s σ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hD : 1 < D) (hs : 1 < s) :
    ContinuousOn (qD H sign D d Δ) (Icc s σ) := by
  exact continuousOn_qD_Icc_of_contract hH sign hD hs



end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
