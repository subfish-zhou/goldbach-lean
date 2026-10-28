import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13HatLayersKappaOne

open Set Filter Topology
namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

noncomputable def perturbation (D d ε t : ℝ) : ℝ :=
  (1 + (t + ε) ^ d / Real.log D) ^ t

/-- For fixed exponent and point, the zero-shift perturbation tends to one. -/
lemma tendsto_fixed_perturbation
    (d t : ℝ) :
    Tendsto (fun D : ℝ => perturbation D d 0 t) atTop (𝓝 1) := by
  have hdiv : Tendsto (fun D : ℝ => t ^ d / Real.log D) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop (t ^ d)
  have hbase : Tendsto (fun D : ℝ => 1 + t ^ d / Real.log D) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hdiv
  simpa [perturbation] using hbase.rpow_const (Or.inl one_ne_zero)

noncomputable def perturbationSlope (D d ε t : ℝ) : ℝ :=
  Real.log (1 + (t + ε) ^ d / Real.log D) +
    t * (d * (t + ε) ^ (d - 1) / Real.log D) /
      (1 + (t + ε) ^ d / Real.log D)

lemma perturbationSlope_le
    {D d ε t σ : ℝ} (hlog : 0 < Real.log D) (hd : 0 ≤ d)
    (ht : 1 ≤ t) (htσ : t ≤ σ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    perturbationSlope D d ε t ≤
      (1 + σ * d) * (σ + 1) ^ d / Real.log D := by
  let x := t + ε
  let u := x ^ d / Real.log D
  have hx1 : 1 ≤ x := by dsimp [x]; linarith
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
  have hu0 : 0 ≤ u := div_nonneg (Real.rpow_nonneg hx0 _) hlog.le
  have hB1 : 1 ≤ 1 + u := by linarith
  have hBpos : 0 < 1 + u := lt_of_lt_of_le (by norm_num) hB1
  have hlogB : Real.log (1 + u) ≤ u := by
    linarith [Real.log_le_sub_one_of_pos hBpos]
  have hxm : x ^ (d - 1) ≤ x ^ d :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hnum0 : 0 ≤ d * x ^ (d - 1) / Real.log D :=
    div_nonneg (mul_nonneg hd (Real.rpow_nonneg hx0 _)) hlog.le
  have hdiv : (d * x ^ (d - 1) / Real.log D) / (1 + u) ≤
      d * x ^ (d - 1) / Real.log D := div_le_self hnum0 hB1
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hσ0 : 0 ≤ σ := ht0.trans htσ
  have hterm1 : (t * (d * x ^ (d - 1) / Real.log D)) / (1 + u) ≤
      σ * (d * x ^ d / Real.log D) := by
    rw [show (t * (d * x ^ (d - 1) / Real.log D)) / (1 + u) =
      t * ((d * x ^ (d - 1) / Real.log D) / (1 + u)) by ring]
    calc
      t * ((d * x ^ (d - 1) / Real.log D) / (1 + u)) ≤
          t * (d * x ^ (d - 1) / Real.log D) :=
        mul_le_mul_of_nonneg_left hdiv ht0
      _ ≤ t * (d * x ^ d / Real.log D) := by
        gcongr
      _ ≤ σ * (d * x ^ d / Real.log D) := by
        gcongr
  have hxσ : x ≤ σ + 1 := by dsimp [x]; linarith
  have hxpow : x ^ d ≤ (σ + 1) ^ d :=
    Real.rpow_le_rpow hx0 hxσ hd
  dsimp [perturbationSlope, x, u] at *
  calc
    Real.log (1 + (t + ε) ^ d / Real.log D) +
        t * (d * (t + ε) ^ (d - 1) / Real.log D) /
          (1 + (t + ε) ^ d / Real.log D) ≤
        (t + ε) ^ d / Real.log D +
          σ * (d * (t + ε) ^ d / Real.log D) := add_le_add hlogB hterm1
    _ = (1 + σ * d) * (t + ε) ^ d / Real.log D := by ring
    _ ≤ (1 + σ * d) * (σ + 1) ^ d / Real.log D := by
      gcongr

private lemma rpow_deriv_factor {B F t : ℝ} (hB : 0 < B) :
    F * t * B ^ (t - 1) + B ^ t * Real.log B =
      B ^ t * (Real.log B + t * F / B) := by
  rw [Real.rpow_sub hB, Real.rpow_one]
  field_simp [ne_of_gt hB]
  ring

lemma hasDerivAt_perturbation
    {D d ε t : ℝ} (hlog : 0 < Real.log D) (hte : 0 < t + ε) :
    HasDerivAt (perturbation D d ε)
      (perturbation D d ε t *
        (Real.log (1 + (t + ε) ^ d / Real.log D) +
          t * (d * (t + ε) ^ (d - 1) / Real.log D) /
            (1 + (t + ε) ^ d / Real.log D))) t := by
  let B : ℝ → ℝ := fun x => 1 + (x + ε) ^ d / Real.log D
  have hpow0 := ((hasDerivAt_id t).add_const ε).rpow_const
    (p := d) (Or.inl (ne_of_gt hte))
  have hpow : HasDerivAt (fun x : ℝ => (x + ε) ^ d)
      (d * (t + ε) ^ (d - 1)) t := by
    convert hpow0 using 1 <;> simp only [id_eq]; ring
  have hB : HasDerivAt B (d * (t + ε) ^ (d - 1) / Real.log D) t := by
    simpa [B] using hpow.div_const (Real.log D) |>.const_add 1
  have hBpos : 0 < B t := by
    dsimp [B]
    have hu : 0 ≤ (t + ε) ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg hte.le _) hlog.le
    linarith
  have hout := hB.rpow (hasDerivAt_id t) hBpos
  have hout' : HasDerivAt (fun x => B x ^ x)
      ((d * (t + ε) ^ (d - 1) / Real.log D) * t * B t ^ (t - 1) +
        B t ^ t * Real.log (B t)) t := by
    simpa only [id_eq, one_mul] using hout
  have hfac := rpow_deriv_factor (B := B t)
    (F := d * (t + ε) ^ (d - 1) / Real.log D) (t := t) hBpos
  rw [show perturbation D d ε = fun x => B x ^ x by rfl]
  change HasDerivAt (fun x => B x ^ x)
    (B t ^ t * (Real.log (B t) +
      t * (d * (t + ε) ^ (d - 1) / Real.log D) / B t)) t
  rw [← hfac]
  exact hout'

lemma hasDerivAt_lambda_of_contract
    {H : Section13HatLayers} {β D d ε t : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hlog : 0 < Real.log D) (hte : 0 < t + ε)
    (hthreshold : β + sign.epsilon < t) :
    HasDerivAt (lambda H sign D d ε)
      (perturbation D d ε t *
        (weightedHat H sign t *
          (Real.log (1 + (t + ε) ^ d / Real.log D) +
            t * (d * (t + ε) ^ (d - 1) / Real.log D) /
              (1 + (t + ε) ^ d / Real.log D)) -
          t * H.T sign.opposite (t - 1))) t := by
  have hfun : lambda H sign D d ε =
      fun x => perturbation D d ε x * weightedHat H sign x := by
    funext x
    simp only [lambda_eq_perturb_mul_weightedHat, perturbation]
  rw [hfun]
  change HasDerivAt (perturbation D d ε * weightedHat H sign)
    (perturbation D d ε t *
      (weightedHat H sign t *
        (Real.log (1 + (t + ε) ^ d / Real.log D) +
          t * (d * (t + ε) ^ (d - 1) / Real.log D) /
            (1 + (t + ε) ^ d / Real.log D)) -
        t * H.T sign.opposite (t - 1))) t
  have hp := hasDerivAt_perturbation (d := d) hlog hte
  have hw := hH.dde sign t hthreshold
  have hprod := hp.mul hw
  rw [show perturbation D d ε t *
      (weightedHat H sign t *
        (Real.log (1 + (t + ε) ^ d / Real.log D) +
          t * (d * (t + ε) ^ (d - 1) / Real.log D) /
            (1 + (t + ε) ^ d / Real.log D)) -
        t * H.T sign.opposite (t - 1)) =
      perturbation D d ε t *
          (Real.log (1 + (t + ε) ^ d / Real.log D) +
            t * (d * (t + ε) ^ (d - 1) / Real.log D) /
              (1 + (t + ε) ^ d / Real.log D)) * weightedHat H sign t +
        perturbation D d ε t * (-t * H.T sign.opposite (t - 1)) by ring]
  exact hprod


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
