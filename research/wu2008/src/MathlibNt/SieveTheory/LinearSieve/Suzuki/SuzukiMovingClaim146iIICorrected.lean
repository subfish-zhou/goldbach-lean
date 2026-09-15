import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingSigmaClaim146iII
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCutoffClaim146iiiSanitized

open Set Filter Topology
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

open BridgeAssembly CutoffCorrectedRatio

set_option maxHeartbeats 1200000

/-!
# Source-correct moving closure of Claims 14.6(i) and (ii)

The old `MovingClaim14_6TailCertificate` is not used: its single `ρ D` must
simultaneously dominate a slope bound growing with the moving endpoint and be
`O(sourceSigma⁻²)`.  The corrected interface records the actual pointwise DDE
comparison, before monotonicity is deduced.  The short T4 interval is handled at
the fixed endpoint `4`, so no incompatible moving-`σ` condition is introduced.
-/

/-- Source-correct pointwise input for the two moving monotonicity claims.
It is a derivative/DDE comparison, not either monotonicity conclusion. -/
def MovingDerivativeDDECertificateOnSource
    (H : Section13HatLayers) (d : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    4 ≤ sourceSigma D d ∧
    ∀ (sign : ErrorSign) (ε t : ℝ),
      (ε = 0 ∨ ε = 1) → 2 + sign.epsilon < t →
      t < sourceSigma D d →
      weightedHat H sign t * perturbationSlope D d ε t ≤
        t * H.T sign.opposite (t - 1)

private lemma corrected_lambda_nonneg
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {D d : ℝ} (hD : 1 < D) (sign : ErrorSign) {t : ℝ} (ht : 0 < t) :
    0 ≤ lambda H sign D d 1 t := by
  rw [lambda_eq_perturb_mul_weightedHat]
  apply mul_nonneg
  · apply Real.rpow_nonneg
    have hu : 0 ≤ (t + 1) ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_pos hD).le
    linarith
  · exact mul_nonneg (sq_nonneg t) (hH.positive sign t ht).le

/-- The corrected source certificate closes both Claims with the required
`∃ D₀, ∀ D ≥ D₀` quantifier order.  The only extra threshold is elementary: it
makes the perturbation slope small on the fixed T4 interval `[2,4]`. -/
theorem eventually_claim14_6_i_ii_at_sourceSigma_of_derivativeDDE
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {d Δ : ℝ} (hd1 : 1 < d) (hΔ : -1 < Δ)
    (hcert : MovingDerivativeDDECertificateOnSource H d) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      Claim14_6_MonotoneLambdaPremise H D d (sourceSigma D d) ∧
      Claim14_6_MonotoneQPremise H D d Δ (sourceSigma D d) := by
  rcases hcert with ⟨Da, hDa, hcert⟩
  let ρ : ℝ := (1 + Δ) / 12
  let C : ℝ := (1 + 4 * d) * 5 ^ d
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have : 0 < 1 + Δ := by linarith
    exact div_pos this (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hfactor : 0 ≤ 1 + 4 * d := by linarith
    exact mul_nonneg hfactor (Real.rpow_nonneg (by norm_num) _)
  let X : ℝ := max 1 (C / ρ)
  let Db : ℝ := Real.exp X
  have hX : 0 < X := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hDb : 1 < Db := by
    dsimp [Db]
    exact Real.one_lt_exp_iff.mpr hX
  let D₀ : ℝ := max Da Db
  refine ⟨D₀, hDa.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hDaD : Da ≤ D := (le_max_left Da Db).trans hD
  have hDbD : Db ≤ D := (le_max_right Da Db).trans hD
  have hD1 : 1 < D := hDa.trans_le hDaD
  have hlog : 0 < Real.log D := Real.log_pos hD1
  rcases hcert D hDaD with ⟨hσ4, hdom⟩
  have hXD : X ≤ Real.log D := by
    apply (Real.le_log_iff_exp_le (zero_lt_one.trans hD1)).2
    simpa [Db] using hDbD
  have hClog : C ≤ ρ * Real.log D := by
    have hCrho : C / ρ ≤ X := le_max_right _ _
    have := hCrho.trans hXD
    simpa [mul_comm] using (div_le_iff₀ hρ).mp this
  have hi : Claim14_6_MonotoneLambdaPremise H D d (sourceSigma D d) :=
    claim14_6_i_of_explicit_derivative_domination hH hlog hdom
  have hi' := hi
  unfold Claim14_6_MonotoneLambdaPremise at hi'
  rw [hH.betaHat_eq] at hi'
  refine ⟨hi, ?_⟩
  unfold Claim14_6_MonotoneQPremise
  rw [hH.betaHat_eq]
  intro sign
  cases sign with
  | plus =>
      have hshift : AntitoneOn
          (fun t => lambda H ErrorSign.minus D d 1 (t - 1))
          (Ioc (2 + 1) (sourceSigma D d)) := by
        intro x hx y hy hxy
        apply hi' ErrorSign.minus 1 (Or.inr rfl)
        · constructor
          · simp [ErrorSign.epsilon]; linarith [hx.1]
          · linarith [hx.2]
        · constructor
          · simp [ErrorSign.epsilon]; linarith [hy.1]
          · linarith [hy.2]
        · linarith
      apply qD_mul_antitoneOn_of_shifted_lambda H ErrorSign.plus D d Δ hΔ.le
        (S := Ioc (2 + 1) (sourceSigma D d))
      · intro t ht
        change 1 < t
        have ht3 : 3 < t := by norm_num at ht ⊢; exact ht.1
        linarith
      · exact hshift
      · intro t ht
        exact corrected_lambda_nonneg hH hD1 ErrorSign.minus (by linarith [ht.1])
  | minus =>
      have hlargeFixed : (1 + 4 * d) * (4 + 1) ^ d ≤ ρ * Real.log D := by
        norm_num [C] at hClog ⊢
        exact hClog
      have hshortFixed : ρ * (4 * (4 - 1)) ≤ 1 + Δ := by
        dsimp [ρ]
        ring_nf
        exact le_rfl
      have hlow : AntitoneOn
          (fun t => qD H ErrorSign.plus D d Δ t * t) (Ioc 2 4) := by
        exact qD_mul_antitoneOn_short_minus
          (H := H) (β := 2) (D := D) (d := d) (Δ := Δ)
          (τ := 4) (σ := 4) (ρ := ρ) hH (by linarith) hΔ.le hρ hlog
          hlargeFixed (by norm_num) (by norm_num) le_rfl hshortFixed
      have hshift : AntitoneOn
          (fun t => lambda H ErrorSign.plus D d 1 (t - 1))
          (Icc 4 (sourceSigma D d)) := by
        intro x hx y hy hxy
        apply hi' ErrorSign.plus 1 (Or.inr rfl)
        · constructor
          · simp [ErrorSign.epsilon]; linarith [hx.1]
          · linarith [hx.2]
        · constructor
          · simp [ErrorSign.epsilon]; linarith [hy.1]
          · linarith [hy.2]
        · linarith
      have hhigh : AntitoneOn
          (fun t => qD H ErrorSign.plus D d Δ t * t)
          (Icc 4 (sourceSigma D d)) := by
        apply qD_mul_antitoneOn_of_shifted_lambda H ErrorSign.minus D d Δ hΔ.le
        · intro t ht
          change 1 < t
          have ht4 : 4 ≤ t := ht.1
          linarith
        · exact hshift
        · intro t ht
          exact corrected_lambda_nonneg hH hD1 ErrorSign.plus (by linarith [ht.1])
      intro x hx y hy hxy
      simp [ErrorSign.epsilon] at hx hy
      by_cases hy4 : y ≤ 4
      · exact hlow ⟨hx.1, hxy.trans hy4⟩ ⟨hy.1, hy4⟩ hxy
      · have h4y : 4 ≤ y := (lt_of_not_ge hy4).le
        by_cases hx4 : x ≤ 4
        · exact (hhigh ⟨le_rfl, hσ4⟩ ⟨h4y, hy.2⟩ h4y).trans
            (hlow ⟨hx.1, hx4⟩ ⟨by norm_num, le_rfl⟩ hx4)
        · exact hhigh ⟨(lt_of_not_ge hx4).le, hx.2⟩ ⟨h4y, hy.2⟩ hxy

/-- The proved Section-13 cutoff majorant supplies the unshifted (`ε=0`) half
of the corrected pointwise certificate through Proposition 13.1's moving
ratio.  The shifted half remains explicit in the corrected interface rather
than being hidden in an impossible scalar `ρ`. -/
theorem eventually_unshifted_derivativeDDE_of_cutoffMajorants
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {d : ℝ} (hd : 0 < d)
    (majorant : ∀ sign,
      CutoffMajorant (section13_bridgeAtThree hH sign).Qhat) :
    ∃ M D₀ : ℝ, 1 < M ∧ 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      M ≤ sourceSigma D d ∧ ∀ sign t, M ≤ t → t ≤ sourceSigma D d →
      weightedHat H sign t * perturbationSlope D d 0 t ≤
        t * H.T sign.opposite (t - 1) := by
  obtain ⟨M, hM, hratio⟩ :=
    exists_common_ratioOnSource_of_cutoffMajorants hH hd majorant
  obtain ⟨Dp, hDp, hp⟩ :=
    movingDDEAsymptoticCertificateOnSource_of_proposition131_ratioOnSource
      hH.toSection13HatContract ErrorSign.plus (hratio ErrorSign.plus)
  obtain ⟨Dm, hDm, hm⟩ :=
    movingDDEAsymptoticCertificateOnSource_of_proposition131_ratioOnSource
      hH.toSection13HatContract ErrorSign.minus (hratio ErrorSign.minus)
  let D₀ := max Dp Dm
  refine ⟨M, D₀, hM, hDp.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hpD := hp D ((le_max_left Dp Dm).trans hD)
  have hmD := hm D ((le_max_right Dp Dm).trans hD)
  refine ⟨hpD.1, ?_⟩
  intro sign t hMt htσ
  have hs : weightedHat H sign t * perturbationSlope D d 0 t ≤
      t * H.T sign.opposite (t - 1) *
        ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)) := by
    cases sign with
    | plus =>
        by_cases hcut : t ≤ (Real.log D) ^ (1 / d)
        · exact hpD.2.1 t hMt hcut htσ
        · exact hpD.2.2 t (lt_of_not_ge hcut) htσ
    | minus =>
        by_cases hcut : t ≤ (Real.log D) ^ (1 / d)
        · exact hmD.2.1 t hMt hcut htσ
        · exact hmD.2.2 t (lt_of_not_ge hcut) htσ
  have hD1 : 1 < D := hDp.trans_le ((le_max_left Dp Dm).trans hD)
  have ht0 : 0 < t := by linarith
  have hA0 : 0 ≤ t * H.T sign.opposite (t - 1) :=
    (mul_pos ht0 (hH.toSection13HatContract.positive sign.opposite (t - 1) (by linarith))).le
  have hz0 : 0 ≤ t ^ d / Real.log D :=
    div_nonneg (Real.rpow_nonneg ht0.le _) (Real.log_pos hD1).le
  have hzle : (t ^ d / Real.log D) / (1 + t ^ d / Real.log D) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  exact hs.trans (mul_le_of_le_one_right hA0 hzle)


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
