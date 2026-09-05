import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma133WeightedTail
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146Integral

open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Claim 14.6(iii), at κ = 1 and on a fixed compact source interval, with no
auxiliary distortion or weighted-tail hypothesis.  The exponent controlling the
limit integrand is `1 - Δ` (positive when `Δ < 1`); this is distinct from the
positive exponent in Suzuki's Lemma 13.3. -/
theorem claim14_6_iii_for_sufficiently_large_D_no_extra_premise
    {H : Section13HatLayers} {β d Δ s σ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hd : 0 ≤ d) (hΔ : Δ < 1)
    (hs : β + sign.epsilon ≤ s) (hsσ : s ≤ σ) :
    ∃ D₀, 1 < D₀ ∧ ∀ D, D₀ ≤ D →
      (∫ t in s..σ, qD H sign.opposite D d Δ t) <
        (1 - 1 / σ) ^ (1 - Δ) * lambda H sign D d 0 s := by
  have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
  have hs1 : 1 < s := by linarith [hH.beta_gt_one]
  have hs0 : 0 < s := zero_lt_one.trans hs1
  rcases hsσ.eq_or_lt with rfl | hsσlt
  · refine ⟨2, by norm_num, ?_⟩
    intro D hD
    exact claim14_6_iii_at_endpoint hH sign (by linarith) hs1
  · have hσ1 : 1 < σ := hs1.trans hsσlt
    have hσ0 : 0 < σ := zero_lt_one.trans hσ1
    let c : ℝ := 1 - 1 / σ
    have hc0 : 0 < c := by
      dsimp [c]
      exact sub_pos.mpr ((div_lt_one hσ0).mpr hσ1)
    have hc1 : c < 1 := by
      dsimp [c]
      have : 0 < 1 / σ := one_div_pos.mpr hσ0
      linarith
    let p : ℝ := 1 - Δ
    have hp : 0 < p := by dsimp [p]; linarith
    let Wₛ : ℝ := weightedHat H sign s
    let Wσ : ℝ := weightedHat H sign σ
    have hWs : 0 < Wₛ := by
      dsimp [Wₛ]
      exact mul_pos (sq_pos_of_pos hs0) (hH.positive sign s hs0)
    have hWσ : 0 < Wσ := by
      dsimp [Wσ]
      exact mul_pos (sq_pos_of_pos hσ0) (hH.positive sign σ hσ0)
    let J : ℝ := Wₛ - Wσ
    have htailcont : ContinuousOn (hatTailIntegrand H sign) (Icc s σ) := by
      apply continuousOn_id.mul
      exact (hH.continuous sign.opposite).comp
        (continuousOn_id.sub continuousOn_const) (by
          intro t ht
          exact sub_pos.mpr (hs1.trans_le ht.1))
    have htailpos : 0 < ∫ t in s..σ, hatTailIntegrand H sign t := by
      apply intervalIntegral.integral_pos hsσlt htailcont
      · intro t ht
        exact (mul_pos (hs0.trans_le ht.1.le)
          (hH.positive sign.opposite (t - 1) (sub_pos.mpr (hs1.trans_le ht.1.le)))).le
      · refine ⟨s, ⟨le_rfl, hsσlt.le⟩, ?_⟩
        exact mul_pos hs0 (hH.positive sign.opposite (s - 1) (sub_pos.mpr hs1))
    have hfinite := integral_hatTailIntegrand_closedThreshold hH sign hs hsσlt.le
    have hJ : 0 < J := by
      dsimp [J, Wₛ, Wσ]
      rw [← hfinite]
      exact htailpos
    let R : ℝ := 1 + Wσ / (2 * J)
    have hR1 : 1 < R := by
      dsimp [R]
      have : 0 < Wσ / (2 * J) := div_pos hWσ (mul_pos (by norm_num) hJ)
      linarith
    have hlogR : 0 < Real.log R := Real.log_pos hR1
    let A : ℝ := σ * σ ^ d
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg hσ0.le (Real.rpow_nonneg hσ0.le _)
    let D₀ : ℝ := Real.exp (A / Real.log R + 1)
    have hD₀ : 1 < D₀ := by
      dsimp [D₀]
      have : 0 ≤ A / Real.log R := div_nonneg hA0 hlogR.le
      exact Real.one_lt_exp_iff.mpr (by linarith)
    refine ⟨D₀, hD₀, ?_⟩
    intro D hD
    have hD1 : 1 < D := hD₀.trans_le hD
    have hlogD : 0 < Real.log D := Real.log_pos hD1
    have hlogmono : Real.log D₀ ≤ Real.log D :=
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) (zero_lt_one.trans hD1) hD
    have hthreshold : A / Real.log R + 1 ≤ Real.log D := by
      simpa [D₀] using hlogmono
    have hAR : A / Real.log R < Real.log D := by linarith
    have hAlarge : A < Real.log R * Real.log D := by
      rw [div_lt_iff₀ hlogR] at hAR
      simpa [mul_comm] using hAR
    let C : ℝ := c ^ p
    have hCpos : 0 < C := by dsimp [C]; exact Real.rpow_pos_of_pos hc0 _
    have hqcont : ContinuousOn (qD H sign.opposite D d Δ) (Icc s σ) :=
      continuousOn_qD_Icc_of_contract hH sign.opposite hD1 hs1
    have hpoint : ∀ t ∈ Icc s σ,
        qD H sign.opposite D d Δ t ≤ R * C * hatTailIntegrand H sign t := by
      intro t ht
      have ht1 : 1 < t := hs1.trans_le ht.1
      have ht0 : 0 < t := zero_lt_one.trans ht1
      have htm0 : 0 < t - 1 := sub_pos.mpr ht1
      let a : ℝ := (t - 1) / t
      have ha0 : 0 < a := div_pos htm0 ht0
      have hatc : a ≤ c := by
        dsimp [a, c]
        rw [div_le_iff₀ ht0, div_eq_mul_inv, sub_mul]
        field_simp [ne_of_gt ht0, ne_of_gt hσ0]
        nlinarith [ht.2]
      have hap : a ^ p ≤ C := by
        dsimp [C]
        exact Real.rpow_le_rpow ha0.le hatc hp.le
      let B : ℝ := 1 + t ^ d / Real.log D
      have htd : t ^ d ≤ σ ^ d := Real.rpow_le_rpow ht0.le ht.2 hd
      have hBpos : 0 < B := by
        dsimp [B]
        have : 0 ≤ t ^ d / Real.log D :=
          div_nonneg (Real.rpow_nonneg ht0.le _) hlogD.le
        linarith
      have hlogB : Real.log B ≤ t ^ d / Real.log D := by
        dsimp [B]
        linarith [Real.log_le_sub_one_of_pos hBpos]
      have hpert_le : (t - 1) * Real.log B ≤ A / Real.log D := by
        calc
          (t - 1) * Real.log B ≤ (t - 1) * (t ^ d / Real.log D) :=
            mul_le_mul_of_nonneg_left hlogB htm0.le
          _ ≤ σ * (σ ^ d / Real.log D) := by
            have htminus_le : t - 1 ≤ σ := by linarith [ht.2]
            gcongr
          _ = A / Real.log D := by dsimp [A]; ring
      have hpertlog : (t - 1) * Real.log B < Real.log R := by
        have : A / Real.log D < Real.log R := by
          rw [div_lt_iff₀ hlogD]
          simpa [mul_comm] using hAlarge
        exact hpert_le.trans_lt this
      have hpert : B ^ (t - 1) < R := by
        have hpowpos : 0 < B ^ (t - 1) := Real.rpow_pos_of_pos hBpos _
        apply (Real.strictMonoOn_log.lt_iff_lt hpowpos (zero_lt_one.trans hR1)).mp
        rw [Real.log_rpow hBpos]
        exact hpertlog
      have htail0 : 0 ≤ hatTailIntegrand H sign t :=
        (mul_pos ht0 (hH.positive sign.opposite (t - 1) htm0)).le
      have hfactor : B ^ (t - 1) * a ^ p ≤ R * C := by
        exact mul_le_mul hpert.le hap (Real.rpow_nonneg ha0.le _)
          (zero_lt_one.trans hR1).le
      have hratio : t / (t - 1) = a⁻¹ := by dsimp [a]; rw [inv_div]
      calc
        qD H sign.opposite D d Δ t =
            (B ^ (t - 1) * a ^ p) * hatTailIntegrand H sign t := by
          simp only [qD, Section13HatLayers.kappaHat]
          norm_num [Real.rpow_one]
          dsimp [B, a, p, hatTailIntegrand]
          rw [show t / (t - 1) = ((t - 1) / t)⁻¹ by rw [inv_div],
              Real.inv_rpow ha0.le, ← Real.rpow_neg ha0.le,
              show 1 - Δ = 1 + (-Δ) by ring, Real.rpow_add ha0,
              Real.rpow_one]
          dsimp [a]
          field_simp [ne_of_gt ht0, ne_of_gt htm0]
        _ ≤ (R * C) * hatTailIntegrand H sign t :=
          mul_le_mul_of_nonneg_right hfactor htail0
    have hmono : (∫ t in s..σ, qD H sign.opposite D d Δ t) ≤
        ∫ t in s..σ, (R * C) * hatTailIntegrand H sign t :=
      intervalIntegral.integral_mono_on hsσlt.le
        (hqcont.intervalIntegrable_of_Icc hsσlt.le)
        ((continuousOn_const.mul htailcont).intervalIntegrable_of_Icc hsσlt.le) hpoint
    have hRJ : R * J = J + Wσ / 2 := by
      dsimp [R]
      field_simp [ne_of_gt hJ]
    have hmargin : R * C * J < C * Wₛ := by
      have : J + Wσ / 2 < Wₛ := by
        dsimp [J]
        linarith [hWσ]
      calc
        R * C * J = C * (R * J) := by ring
        _ = C * (J + Wσ / 2) := by rw [hRJ]
        _ < C * Wₛ := mul_lt_mul_of_pos_left this hCpos
    have hperturb_s : 1 ≤ (1 + s ^ d / Real.log D) ^ s := by
      apply Real.one_le_rpow
      · have : 0 ≤ s ^ d / Real.log D :=
          div_nonneg (Real.rpow_nonneg hs0.le _) hlogD.le
        linarith
      · exact hs0.le
    have hWs_lambda : Wₛ ≤ lambda H sign D d 0 s := by
      rw [lambda_eq_perturb_mul_weightedHat]
      norm_num
      exact le_mul_of_one_le_left hWs.le hperturb_s
    calc
      (∫ t in s..σ, qD H sign.opposite D d Δ t) ≤
          ∫ t in s..σ, (R * C) * hatTailIntegrand H sign t := hmono
      _ = R * C * J := by
        rw [intervalIntegral.integral_const_mul]
        dsimp [J, Wₛ, Wσ]
        rw [hfinite]
      _ < C * Wₛ := hmargin
      _ ≤ (1 - 1 / σ) ^ (1 - Δ) * lambda H sign D d 0 s := by
        dsimp [C, c, p]
        exact mul_le_mul_of_nonneg_left hWs_lambda
          (Real.rpow_nonneg hc0.le _)


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
