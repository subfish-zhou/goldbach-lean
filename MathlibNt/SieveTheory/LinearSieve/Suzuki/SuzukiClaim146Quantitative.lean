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

theorem lambda_antitoneOn_Icc_of_log_bound
    {H : Section13HatLayers} {β D d ε σ ρ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hd : 0 ≤ d) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hσ : β + sign.epsilon ≤ σ) (_hρ : 0 < ρ)
    (hlog : 0 < Real.log D)
    (hDlarge : (1 + σ * d) * (σ + 1) ^ d ≤ ρ * Real.log D)
    (hdelay : ∀ t, β + sign.epsilon < t → t ≤ σ →
      ρ * weightedHat H sign t ≤ t * H.T sign.opposite (t - 1)) :
    AntitoneOn (lambda H sign D d ε) (Icc (β + sign.epsilon) σ) := by
  have hleft : 1 < β + sign.epsilon := by
    have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
    linarith [hH.beta_gt_one]
  have hfun : lambda H sign D d ε =
      fun x => perturbation D d ε x * weightedHat H sign x := by
    funext x
    simp only [lambda_eq_perturb_mul_weightedHat, perturbation]
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · rw [hfun]
    have hp : ContinuousOn (perturbation D d ε) (Icc (β + sign.epsilon) σ) := by
      intro (t : ℝ) (ht : t ∈ Icc (β + sign.epsilon) σ)
      have ht0 : 0 < t := lt_of_lt_of_le (zero_lt_one.trans hleft) ht.1
      have hte : 0 < t + ε := add_pos_of_pos_of_nonneg ht0 hε0
      exact (hasDerivAt_perturbation (d := d) hlog hte).continuousAt.continuousWithinAt
    exact hp.mul ((continuousOn_id.pow 2).mul ((hH.continuous sign).mono (by
      intro (t : ℝ) (ht : t ∈ Icc (β + sign.epsilon) σ)
      exact lt_of_lt_of_le (zero_lt_one.trans hleft) ht.1)))
  · intro t ht
    have htI : t ∈ Icc (β + sign.epsilon) σ := interior_subset ht
    have htstrict : β + sign.epsilon < t := by
      rw [interior_Icc] at ht
      exact ht.1
    have ht0 : 0 < t := (zero_lt_one.trans hleft).trans htstrict
    have hte : 0 < t + ε := add_pos_of_pos_of_nonneg ht0 hε0
    exact (hasDerivAt_lambda_of_contract hH sign hlog hte htstrict).differentiableAt.differentiableWithinAt
  · intro t ht
    have htI : t ∈ Icc (β + sign.epsilon) σ := interior_subset ht
    have htstrict : β + sign.epsilon < t := by
      rw [interior_Icc] at ht
      exact ht.1
    have ht0 : 0 < t := (zero_lt_one.trans hleft).trans htstrict
    have hte : 0 < t + ε := add_pos_of_pos_of_nonneg ht0 hε0
    have ht1 : 1 ≤ t := le_of_lt (hleft.trans htstrict)
    have hslope := perturbationSlope_le hlog hd ht1 htI.2 hε0 hε1
    have hC : (1 + σ * d) * (σ + 1) ^ d / Real.log D ≤ ρ :=
      (div_le_iff₀ hlog).2 (by simpa [mul_comm] using hDlarge)
    have hslopeρ : perturbationSlope D d ε t ≤ ρ := hslope.trans hC
    have hW0 : 0 ≤ weightedHat H sign t := by
      exact mul_nonneg (sq_nonneg t) (le_of_lt (hH.positive sign t ht0))
    have hbracket : weightedHat H sign t * perturbationSlope D d ε t -
        t * H.T sign.opposite (t - 1) ≤ 0 := by
      have := (mul_le_mul_of_nonneg_left hslopeρ hW0).trans
        (by simpa [mul_comm] using hdelay t htstrict htI.2)
      linarith
    have hp0 : 0 ≤ perturbation D d ε t := by
      exact (Real.rpow_nonneg (by
        have hu : 0 ≤ (t + ε) ^ d / Real.log D :=
          div_nonneg (Real.rpow_nonneg hte.le _) hlog.le
        linarith) _)
    rw [(hasDerivAt_lambda_of_contract hH sign hlog hte htstrict).deriv]
    change perturbation D d ε t *
      (weightedHat H sign t * perturbationSlope D d ε t -
        t * H.T sign.opposite (t - 1)) ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos hp0 hbracket

/-- On a compact Section 13 interval, positivity and continuity give a
uniform positive lower bound for the delayed-to-current ratio. -/
lemma exists_delayRatioMargin
    {H : Section13HatLayers} {β σ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hσ : β + sign.epsilon ≤ σ) :
    ∃ ρ, 0 < ρ ∧ ∀ t, β + sign.epsilon ≤ t → t ≤ σ →
      ρ * weightedHat H sign t ≤ t * H.T sign.opposite (t - 1) := by
  let S : Set ℝ := Icc (β + sign.epsilon) σ
  let R : ℝ → ℝ := fun t =>
    (t * H.T sign.opposite (t - 1)) / weightedHat H sign t
  have htpos : ∀ t ∈ S, 0 < t := by
    intro t ht
    have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
    exact lt_of_lt_of_le (by linarith [hH.beta_gt_one]) ht.1
  have hshift : ∀ t ∈ S, 0 < t - 1 := by
    intro t ht
    have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
    linarith [hH.beta_gt_one, ht.1]
  have hWpos : ∀ t ∈ S, 0 < weightedHat H sign t := by
    intro t ht
    exact mul_pos (sq_pos_of_pos (htpos t ht))
      (hH.positive sign t (htpos t ht))
  have hRcont : ContinuousOn R S := by
    apply ContinuousOn.div
    · exact continuousOn_id.mul ((hH.continuous sign.opposite).comp
        (continuousOn_id.sub continuousOn_const) (fun t ht => hshift t ht))
    · exact (continuousOn_id.pow 2).mul
        ((hH.continuous sign).mono (fun t ht => htpos t ht))
    · exact fun t ht => ne_of_gt (hWpos t ht)
  have hSne : S.Nonempty := ⟨β + sign.epsilon, by exact ⟨le_rfl, hσ⟩⟩
  obtain ⟨x, hxS, hxmin⟩ := isCompact_Icc.exists_isMinOn hSne hRcont
  refine ⟨R x, ?_, ?_⟩
  · exact div_pos (mul_pos (htpos x hxS)
      (hH.positive sign.opposite (x - 1) (hshift x hxS))) (hWpos x hxS)
  · intro t htl htu
    have htS : t ∈ S := ⟨htl, htu⟩
    exact (le_div_iff₀ (hWpos t htS)).mp (hxmin htS)

/-- The two signs admit one common positive delay-ratio margin on their compact
intervals.  This discharges the old source-level `hdelay` premise internally. -/
theorem exists_common_delayRatioMargin
    {H : Section13HatLayers} {β σ : ℝ}
    (hH : Section13HatContract H β)
    (hσ : ∀ sign : ErrorSign, β + sign.epsilon ≤ σ) :
    ∃ ρ, 0 < ρ ∧ ∀ sign t, β + sign.epsilon < t → t ≤ σ →
      ρ * weightedHat H sign t ≤ t * H.T sign.opposite (t - 1) := by
  obtain ⟨ρp, hρp, hp⟩ := exists_delayRatioMargin hH .plus (hσ .plus)
  obtain ⟨ρm, hρm, hm⟩ := exists_delayRatioMargin hH .minus (hσ .minus)
  refine ⟨min ρp ρm, lt_min hρp hρm, ?_⟩
  intro sign t htl htu
  have ht0 : 0 ≤ weightedHat H sign t := by
    have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
    have htpos : 0 < t := by linarith [hH.beta_gt_one, htl]
    exact mul_nonneg (sq_nonneg t) (le_of_lt (hH.positive sign t htpos))
  cases sign with
  | plus =>
      exact (mul_le_mul_of_nonneg_right (min_le_left ρp ρm) ht0).trans
        (hp t htl.le htu)
  | minus =>
      exact (mul_le_mul_of_nonneg_right (min_le_right ρp ρm) ht0).trans
        (hm t htl.le htu)

/-- Quantitative Claim 14.6(i): one common delay-ratio margin `ρ` works for
both `ε=0,1`; the displayed lower bound on `log D` is sufficient. -/
theorem claim14_6_i_of_log_bound
    {H : Section13HatLayers} {β D d σ ρ : ℝ}
    (hH : Section13HatContract H β) (hd : 0 ≤ d)
    (hσ : ∀ sign : ErrorSign, β + sign.epsilon ≤ σ) (hρ : 0 < ρ)
    (hlog : 0 < Real.log D)
    (hDlarge : (1 + σ * d) * (σ + 1) ^ d ≤ ρ * Real.log D)
    (hdelay : ∀ sign t, β + sign.epsilon < t → t ≤ σ →
      ρ * weightedHat H sign t ≤ t * H.T sign.opposite (t - 1)) :
    ∀ sign ε, ε = 0 ∨ ε = 1 →
      AntitoneOn (lambda H sign D d ε) (Icc (β + sign.epsilon) σ) := by
  intro sign ε hε
  rcases hε with rfl | rfl
  · exact lambda_antitoneOn_Icc_of_log_bound hH sign hd (by norm_num) (by norm_num)
      (hσ sign) hρ hlog hDlarge (hdelay sign)
  · exact lambda_antitoneOn_Icc_of_log_bound hH sign hd (by norm_num) (by norm_num)
      (hσ sign) hρ hlog hDlarge (hdelay sign)

/-- Claim 14.6(i) with no external delay-margin premise: Section 13 positivity
and continuity first produce a common margin for both signs, and every `D`
beyond an explicit existential threshold makes both `ε = 0,1` lambda factors
antitone on their compact intervals. -/
theorem claim14_6_i_for_sufficiently_large_D
    {H : Section13HatLayers} {β d σ : ℝ}
    (hH : Section13HatContract H β) (hd : 0 ≤ d)
    (hσ : ∀ sign : ErrorSign, β + sign.epsilon ≤ σ) :
    ∃ D₀, 1 < D₀ ∧ ∀ D, D₀ ≤ D →
      ∀ sign ε, ε = 0 ∨ ε = 1 →
        AntitoneOn (lambda H sign D d ε) (Icc (β + sign.epsilon) σ) := by
  obtain ⟨ρ, hρ, hdelay⟩ := exists_common_delayRatioMargin hH hσ
  let C : ℝ := (1 + σ * d) * (σ + 1) ^ d
  have hσpos : 0 < σ := by
    have hm := hσ (.minus)
    simp [ErrorSign.epsilon] at hm
    linarith [hH.beta_gt_one]
  have hC0 : 0 ≤ C := by
    apply mul_nonneg
    · nlinarith
    · exact Real.rpow_nonneg (by linarith [hσpos]) _
  let x : ℝ := C / ρ + 1
  have hxpos : 0 < x := by
    dsimp [x]
    have : 0 ≤ C / ρ := div_nonneg hC0 hρ.le
    linarith
  let D₀ : ℝ := Real.exp x
  have hD₀ : 1 < D₀ := by
    dsimp [D₀]
    rw [← Real.exp_zero, Real.exp_lt_exp]
    exact hxpos
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD
  have hD1 : 1 < D := hD₀.trans_le hD
  have hlog : 0 < Real.log D := Real.log_pos hD1
  have hlogmono : Real.log D₀ ≤ Real.log D :=
    Real.strictMonoOn_log.monotoneOn (Real.exp_pos x)
      (zero_lt_one.trans hD1) hD
  have hlogx : x ≤ Real.log D := by
    simpa [D₀] using hlogmono
  have hCx : C ≤ ρ * x := by
    have hbase : C ≤ C + ρ := by linarith
    calc
      C ≤ C + ρ := hbase
      _ = ρ * x := by
        dsimp [x]
        field_simp [ne_of_gt hρ]
  have hDlarge : C ≤ ρ * Real.log D :=
    hCx.trans (mul_le_mul_of_nonneg_left hlogx hρ.le)
  exact claim14_6_i_of_log_bound hH hd hσ hρ hlog
    (by simpa only [C] using hDlarge) hdelay

end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
