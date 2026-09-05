import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13HatLayersKappaOne

open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Local continuity of `qD`, using only the Section 13 contract on the positive axis. -/
lemma continuousOn_qD_Icc_of_contract
    {H : Section13HatLayers} {β D d Δ s σ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hD : 1 < D) (hs : 1 < s) :
    ContinuousOn (qD H sign D d Δ) (Icc s σ) := by
  unfold qD
  have hlog : 0 < Real.log D := Real.log_pos hD
  have htpos : ∀ t ∈ Icc s σ, 0 < t := fun t ht => (zero_lt_one.trans hs).trans_le ht.1
  have htmpos : ∀ t ∈ Icc s σ, 0 < t - 1 := fun t ht => sub_pos.mpr (hs.trans_le ht.1)
  have htpow : ContinuousOn (fun t : ℝ => t ^ d) (Icc s σ) :=
    continuousOn_id.rpow continuousOn_const (fun t ht => Or.inl (ne_of_gt (htpos t ht)))
  have hbase : ContinuousOn (fun t : ℝ => 1 + t ^ d / Real.log D) (Icc s σ) :=
    continuousOn_const.add (htpow.div_const _)
  have hbasePos : ∀ t ∈ Icc s σ, 0 < 1 + t ^ d / Real.log D := by
    intro t ht
    have : 0 ≤ t ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg (htpos t ht).le _) hlog.le
    linarith
  have houter : ContinuousOn
      (fun t : ℝ => (1 + t ^ d / Real.log D) ^ (t - 1)) (Icc s σ) :=
    hbase.rpow (continuousOn_id.sub continuousOn_const)
      (fun t ht => Or.inl (ne_of_gt (hbasePos t ht)))
  have hshift : ContinuousOn (fun t : ℝ => (t - 1) ^ (H.kappaHat - 1 + 1))
      (Icc s σ) :=
    (continuousOn_id.sub continuousOn_const).rpow continuousOn_const
      (fun t ht => Or.inl (ne_of_gt (htmpos t ht)))
  have hratio : ContinuousOn (fun t : ℝ => t / (t - 1)) (Icc s σ) :=
    continuousOn_id.div (continuousOn_id.sub continuousOn_const)
      (fun t ht => ne_of_gt (htmpos t ht))
  have hratioPow : ContinuousOn (fun t : ℝ => (t / (t - 1)) ^ Δ) (Icc s σ) :=
    hratio.rpow continuousOn_const (fun t ht =>
      Or.inl (ne_of_gt (div_pos (htpos t ht) (htmpos t ht))))
  have hTshift : ContinuousOn (fun t : ℝ => H.T sign (t - 1)) (Icc s σ) := by
    exact (hH.continuous sign).comp (continuousOn_id.sub continuousOn_const) (by
      intro t ht
      exact sub_pos.mpr (hs.trans_le ht.1))
  exact ((houter.mul hshift).mul hTshift).mul hratioPow
/-- Source-faithful replacement for the invalid closed-interval local reduction.
The first premise is the elementary large-`D` distortion estimate; the second is
exactly the finite-interval consequence of the Lemma 13.3 strict weighted-tail
bound.  Together they imply Claim 14.6(iii) directly. -/
theorem claim14_6_iii_of_lemma13_3_style_bound
    {H : Section13HatLayers} {β D d Δ θ s σ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hD : 1 < D) (hσ : 1 < σ)
    (hs : β + sign.epsilon < s) (hsσ : s ≤ σ)
    (hDlarge : ∀ t ∈ Icc s σ,
      (1 + t ^ d / Real.log D) ^ (t - 1) * (t / (t - 1)) ^ Δ ≤
        (((1 - 1 / σ) ^ (1 - Δ) * (1 + s ^ d / Real.log D) ^ s) *
          (((t - 1) / t) ^ θ * (t / (t - 1)))))
    (hlemma13_3 :
      (∫ t in s..σ, ((t - 1) / t) ^ θ * hatTailIntegrand H sign t) <
        weightedHat H sign s) :
    (∫ t in s..σ, qD H sign.opposite D d Δ t) <
      (1 - 1 / σ) ^ (1 - Δ) * lambda H sign D d 0 s := by
  let C : ℝ := (1 - 1 / σ) ^ (1 - Δ) * (1 + s ^ d / Real.log D) ^ s
  let w : ℝ → ℝ := fun t => ((t - 1) / t) ^ θ * hatTailIntegrand H sign t
  have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
  have hs1 : 1 < s := by linarith [hH.beta_gt_one]
  have hqcont : ContinuousOn (qD H sign.opposite D d Δ) (Icc s σ) :=
    continuousOn_qD_Icc_of_contract hH sign.opposite hD hs1
  have htcont : ContinuousOn (hatTailIntegrand H sign) (Icc s σ) := by
    unfold hatTailIntegrand
    apply continuousOn_id.mul
    exact (hH.continuous sign.opposite).comp
      (continuousOn_id.sub continuousOn_const) (by
        intro t ht
        exact sub_pos.mpr (hs1.trans_le ht.1))
  have hratio : ContinuousOn (fun t : ℝ => (t - 1) / t) (Icc s σ) :=
    (continuousOn_id.sub continuousOn_const).div continuousOn_id (by
      intro t ht
      exact ne_of_gt ((zero_lt_one.trans hs1).trans_le ht.1))
  have hwcont : ContinuousOn w (Icc s σ) := by
    apply (hratio.rpow continuousOn_const _).mul htcont
    intro t ht
    left
    exact ne_of_gt (div_pos (sub_pos.mpr (hs1.trans_le ht.1))
      ((zero_lt_one.trans hs1).trans_le ht.1))
  have hpoint : ∀ t ∈ Icc s σ,
      qD H sign.opposite D d Δ t ≤ C * w t := by
    intro t ht
    have ht1 : 1 < t := hs1.trans_le ht.1
    have htm : 0 < t - 1 := sub_pos.mpr ht1
    have hT : 0 < H.T sign.opposite (t - 1) := hH.positive _ _ htm
    have hmul := mul_le_mul_of_nonneg_right (hDlarge t ht) (mul_pos htm hT).le
    have hratio_cancel :
        (t / (t - 1)) * ((t - 1) * H.T sign.opposite (t - 1)) =
          t * H.T sign.opposite (t - 1) := by
      field_simp [ne_of_gt htm]
    calc
      qD H sign.opposite D d Δ t =
          ((1 + t ^ d / Real.log D) ^ (t - 1) * (t / (t - 1)) ^ Δ) *
            ((t - 1) * H.T sign.opposite (t - 1)) := by
        simp only [qD, Section13HatLayers.kappaHat]
        norm_num [Real.rpow_one]
        ring
      _ ≤ (C * (((t - 1) / t) ^ θ * (t / (t - 1)))) *
            ((t - 1) * H.T sign.opposite (t - 1)) := hmul
      _ = C * w t := by
        dsimp [w]
        rw [show C * (((t - 1) / t) ^ θ * (t / (t - 1))) =
          (C * ((t - 1) / t) ^ θ) * (t / (t - 1)) by ring,
          mul_assoc, hratio_cancel]
        unfold hatTailIntegrand
        ring
  have hmono : (∫ t in s..σ, qD H sign.opposite D d Δ t) ≤
      ∫ t in s..σ, C * w t :=
    intervalIntegral.integral_mono_on hsσ
      (hqcont.intervalIntegrable_of_Icc hsσ)
      ((continuousOn_const.mul hwcont).intervalIntegrable_of_Icc hsσ) hpoint
  have hCpos : 0 < C := by
    dsimp [C]
    apply mul_pos
    · apply Real.rpow_pos_of_pos
      have hσ0 : 0 < σ := zero_lt_one.trans hσ
      exact sub_pos.mpr ((div_lt_one hσ0).mpr hσ)
    · apply Real.rpow_pos_of_pos
      have hlog : 0 < Real.log D := Real.log_pos hD
      have hs0 : 0 ≤ s := (zero_lt_one.trans hs1).le
      have : 0 ≤ s ^ d / Real.log D :=
        div_nonneg (Real.rpow_nonneg hs0 _) hlog.le
      linarith
  have hstrict : (∫ t in s..σ, C * w t) < C * weightedHat H sign s := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_lt_mul_of_pos_left hlemma13_3 hCpos
  calc
    (∫ t in s..σ, qD H sign.opposite D d Δ t) <
        C * weightedHat H sign s := hmono.trans_lt hstrict
    _ = (1 - 1 / σ) ^ (1 - Δ) * lambda H sign D d 0 s := by
      dsimp [C]
      rw [lambda_eq_perturb_mul_weightedHat]
      norm_num
      ring

/-- Although the local predicate fails when `s = σ`, Claim 14.6(iii) itself
is immediate there because its right-hand side is strictly positive. -/
theorem claim14_6_iii_at_endpoint
    {H : Section13HatLayers} {β D d Δ σ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hD : 1 < D) (hσ : 1 < σ) :
    (∫ t in σ..σ, qD H sign.opposite D d Δ t) <
      (1 - 1 / σ) ^ (1 - Δ) * lambda H sign D d 0 σ := by
  have hcut : 0 < (1 - 1 / σ) ^ (1 - Δ) := by
    apply Real.rpow_pos_of_pos
    have hσ0 : 0 < σ := zero_lt_one.trans hσ
    exact sub_pos.mpr ((div_lt_one hσ0).mpr hσ)
  have hlam : 0 < lambda H sign D d 0 σ :=
    lambda_pos H sign hD (by norm_num) (zero_lt_one.trans hσ)
      (hH.positive sign σ (zero_lt_one.trans hσ))
  rw [intervalIntegral.integral_same]
  exact mul_pos hcut hlam

end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
