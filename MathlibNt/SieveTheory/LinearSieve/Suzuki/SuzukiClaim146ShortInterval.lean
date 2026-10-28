import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146Quantitative

open Set Filter Topology
namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

private lemma hasDerivAt_shifted_perturbation
    {D d t : ℝ} (hlog : 0 < Real.log D) (ht : 1 < t) :
    HasDerivAt (fun x => perturbation D d 1 (x - 1))
      (perturbation D d 1 (t - 1) * perturbationSlope D d 1 (t - 1)) t := by
  simpa only [Function.comp_def, id_eq, one_mul, mul_one, perturbationSlope, sub_add_cancel] using
    ((hasDerivAt_perturbation (D := D) (d := d) (ε := 1)
      (t := t - 1) hlog (by linarith)).comp t ((hasDerivAt_id t).sub_const 1))

private lemma hasDerivAt_ratio_rpow
    {Δ t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => (x / (x - 1)) ^ (1 + Δ))
      (-((1 + Δ) * (t / (t - 1)) ^ (1 + Δ) / (t * (t - 1)))) t := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have htm0 : 0 < t - 1 := sub_pos.mpr ht
  have hr : 0 < t / (t - 1) := div_pos ht0 htm0
  have hq : HasDerivAt (fun x : ℝ => x / (x - 1)) (-1 / (t - 1) ^ 2) t := by
    have h' : HasDerivAt (fun x : ℝ => x / (x - 1))
        ((1 * (t - 1) - t * 1) / (t - 1) ^ 2) t :=
      (hasDerivAt_id t).div ((hasDerivAt_id t).sub_const 1) (ne_of_gt htm0)
    apply h'.congr_deriv
    ring
  have hp := hq.rpow_const (p := 1 + Δ) (Or.inl (ne_of_gt hr))
  convert hp using 1
  rw [Real.rpow_sub_one (ne_of_gt hr)]
  field_simp [ne_of_gt ht0, ne_of_gt htm0, ne_of_gt hr]

/-- The slope estimate needed on Suzuki's T4 interval.  Unlike the high-range
version, the shifted argument `u = t - 1` need only be nonnegative; the base
`u + 1` is still at least one. -/
lemma perturbationSlope_shift_one_le
    {D d u σ : ℝ} (hlog : 0 < Real.log D) (hd : 0 ≤ d)
    (hu : 0 ≤ u) (huσ : u ≤ σ) :
    perturbationSlope D d 1 u ≤
      (1 + σ * d) * (σ + 1) ^ d / Real.log D := by
  let x := u + 1
  let z := x ^ d / Real.log D
  have hx1 : 1 ≤ x := by dsimp [x]; linarith
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hz0 : 0 ≤ z := div_nonneg (Real.rpow_nonneg hx0 _) hlog.le
  have hB1 : 1 ≤ 1 + z := by linarith
  have hlogB : Real.log (1 + z) ≤ z := by
    linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num) hB1)]
  have hxm : x ^ (d - 1) ≤ x ^ d :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hnum0 : 0 ≤ d * x ^ (d - 1) / Real.log D :=
    div_nonneg (mul_nonneg hd (Real.rpow_nonneg hx0 _)) hlog.le
  have hdiv : (d * x ^ (d - 1) / Real.log D) / (1 + z) ≤
      d * x ^ (d - 1) / Real.log D := div_le_self hnum0 hB1
  have hσ0 : 0 ≤ σ := hu.trans huσ
  have hterm : u * (d * x ^ (d - 1) / Real.log D) / (1 + z) ≤
      σ * (d * x ^ d / Real.log D) := by
    rw [show u * (d * x ^ (d - 1) / Real.log D) / (1 + z) =
      u * ((d * x ^ (d - 1) / Real.log D) / (1 + z)) by ring]
    calc
      _ ≤ u * (d * x ^ (d - 1) / Real.log D) :=
        mul_le_mul_of_nonneg_left hdiv hu
      _ ≤ u * (d * x ^ d / Real.log D) := by gcongr
      _ ≤ σ * (d * x ^ d / Real.log D) := by gcongr
  have hxσ : x ≤ σ + 1 := by dsimp [x]; linarith
  have hxpow : x ^ d ≤ (σ + 1) ^ d := Real.rpow_le_rpow hx0 hxσ hd
  dsimp [perturbationSlope, x, z] at *
  calc
    Real.log (1 + (u + 1) ^ d / Real.log D) +
        u * (d * (u + 1) ^ (d - 1) / Real.log D) /
          (1 + (u + 1) ^ d / Real.log D) ≤
        (u + 1) ^ d / Real.log D +
          σ * (d * (u + 1) ^ d / Real.log D) := add_le_add hlogB hterm
    _ = (1 + σ * d) * (u + 1) ^ d / Real.log D := by ring
    _ ≤ (1 + σ * d) * (σ + 1) ^ d / Real.log D := by gcongr

lemma qD_mul_eq_short_minus
    {H : Section13HatLayers} {β D d Δ t : ℝ}
    (hH : Section13HatContract H β) (ht : 1 < t) (htop : t ≤ β + 2) :
    qD H ErrorSign.plus D d Δ t * t =
      (β - 1) * perturbation D d 1 (t - 1) *
        (t / (t - 1)) ^ (1 + Δ) := by
  rw [← equation14_15 H ErrorSign.plus D d Δ t ht]
  rw [lambda_eq_perturb_mul_weightedHat]
  rw [hH.initial_plus (t - 1) (by linarith) (by linarith)]
  simp only [perturbation]
  ring


lemma qD_mul_antitoneOn_short_minus
    {H : Section13HatLayers} {β D d Δ τ σ ρ : ℝ}
    (hH : Section13HatContract H β)
    (hd : 0 ≤ d) (_hΔ : -1 ≤ Δ) (hρ : 0 < ρ)
    (hlog : 0 < Real.log D)
    (hDlarge : (1 + σ * d) * (σ + 1) ^ d ≤ ρ * Real.log D)
    (hτlower : β ≤ τ) (hτupper : τ ≤ β + 2) (hτσ : τ ≤ σ)
    (hshort : ρ * (σ * (σ - 1)) ≤ 1 + Δ) :
    AntitoneOn (fun t => qD H ErrorSign.plus D d Δ t * t) (Ioc β τ) := by
  have hβ1 : 1 < β := hH.beta_gt_one
  let f : ℝ → ℝ := fun t =>
    (β - 1) * perturbation D d 1 (t - 1) * (t / (t - 1)) ^ (1 + Δ)
  have hEq : ∀ t ∈ Ioc β τ, qD H ErrorSign.plus D d Δ t * t = f t := by
    intro t ht
    exact qD_mul_eq_short_minus hH (hβ1.trans ht.1) (ht.2.trans hτupper)
  have hf : AntitoneOn f (Icc β τ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc β τ)
    · intro t ht
      have ht1 : 1 < t := hβ1.trans_le ht.1
      exact ((((hasDerivAt_shifted_perturbation hlog ht1).const_mul (β - 1)).mul
        (hasDerivAt_ratio_rpow ht1)).continuousAt.continuousWithinAt)
    · intro t ht
      have htI : t ∈ Icc β τ := interior_subset ht
      have ht1 : 1 < t := hβ1.trans_le htI.1
      exact (((hasDerivAt_shifted_perturbation hlog ht1).const_mul (β - 1)).mul
        (hasDerivAt_ratio_rpow ht1)).differentiableAt.differentiableWithinAt
    · intro t ht
      have htI : t ∈ Icc β τ := interior_subset ht
      have htβ : β < t := by
        rw [interior_Icc] at ht
        exact ht.1
      have ht1 : 1 < t := hβ1.trans htβ
      have htσ : t ≤ σ := htI.2.trans hτσ
      have hslope := perturbationSlope_shift_one_le (D := D) (d := d)
        (u := t - 1) (σ := σ) hlog hd (by linarith) (by linarith)
      have hC : (1 + σ * d) * (σ + 1) ^ d / Real.log D ≤ ρ :=
        (div_le_iff₀ hlog).2 (by simpa [mul_comm] using hDlarge)
      have hslopeρ : perturbationSlope D d 1 (t - 1) ≤ ρ := hslope.trans hC
      have htt : 0 < t * (t - 1) := mul_pos (zero_lt_one.trans ht1) (sub_pos.mpr ht1)
      have httσ : t * (t - 1) ≤ σ * (σ - 1) := by nlinarith
      have hratio : ρ ≤ (1 + Δ) / (t * (t - 1)) := by
        rw [le_div_iff₀ htt]
        calc
          ρ * (t * (t - 1)) ≤ ρ * (σ * (σ - 1)) :=
            mul_le_mul_of_nonneg_left httσ hρ.le
          _ ≤ 1 + Δ := hshort
      have hbracket : perturbationSlope D d 1 (t - 1) -
          (1 + Δ) / (t * (t - 1)) ≤ 0 := by linarith
      have hp0 : 0 ≤ perturbation D d 1 (t - 1) := by
        apply Real.rpow_nonneg
        have : 0 ≤ t ^ d / Real.log D :=
          div_nonneg (Real.rpow_nonneg (zero_lt_one.trans ht1).le _) hlog.le
        simpa [perturbation] using (show 0 ≤ 1 + t ^ d / Real.log D by linarith)
      have hr0 : 0 ≤ (t / (t - 1)) ^ (1 + Δ) := Real.rpow_nonneg
        (div_nonneg (zero_lt_one.trans ht1).le (sub_pos.mpr ht1).le) _
      have hβ0 : 0 ≤ β - 1 := by linarith
      have hderiv : deriv f t =
          ((β - 1) * perturbation D d 1 (t - 1)) *
              perturbationSlope D d 1 (t - 1) * (t / (t - 1)) ^ (1 + Δ) +
            ((β - 1) * perturbation D d 1 (t - 1)) *
              (-((1 + Δ) * (t / (t - 1)) ^ (1 + Δ) / (t * (t - 1)))) := by
        have hraw := (((hasDerivAt_shifted_perturbation
          (D := D) (d := d) (t := t) hlog ht1).const_mul (β - 1)).mul
          (hasDerivAt_ratio_rpow (Δ := Δ) (t := t) ht1)).deriv
        change deriv ((fun y => (β - 1) * perturbation D d 1 (y - 1)) *
          fun x => (x / (x - 1)) ^ (1 + Δ)) t = _
        rw [hraw]
        ring
      rw [hderiv]
      rw [show ((β - 1) * perturbation D d 1 (t - 1)) *
              perturbationSlope D d 1 (t - 1) * (t / (t - 1)) ^ (1 + Δ) +
            ((β - 1) * perturbation D d 1 (t - 1)) *
              (-((1 + Δ) * (t / (t - 1)) ^ (1 + Δ) / (t * (t - 1)))) =
          (β - 1) * perturbation D d 1 (t - 1) *
            (t / (t - 1)) ^ (1 + Δ) *
              (perturbationSlope D d 1 (t - 1) - (1 + Δ) / (t * (t - 1))) by ring]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg hβ0 hp0) hr0) hbracket
  intro x hx y hy hxy
  change qD H ErrorSign.plus D d Δ y * y ≤ qD H ErrorSign.plus D d Δ x * x
  rw [hEq x hx, hEq y hy]
  exact hf ⟨hx.1.le, hx.2⟩ ⟨hy.1.le, hy.2⟩ hxy


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
