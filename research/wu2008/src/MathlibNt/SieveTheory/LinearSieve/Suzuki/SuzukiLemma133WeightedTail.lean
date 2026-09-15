import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13HatLayersKappaOne

open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Finite DDE identity valid also at the closed threshold.  The production
identity asks for a strict lower-bound hypothesis only because it differentiates
at the left endpoint; the FTC needs the DDE only in the open interval. -/
lemma integral_hatTailIntegrand_closedThreshold
    {H : Section13HatLayers} {β a b : ℝ} (hH : Section13HatContract H β)
    (sign : ErrorSign) (ha : β + sign.epsilon ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, hatTailIntegrand H sign t) =
      weightedHat H sign a - weightedHat H sign b := by
  let g : ℝ → ℝ := fun t => hatTailIntegrand H sign t
  let f : ℝ → ℝ := -weightedHat H sign
  have heps : 0 ≤ sign.epsilon := by
    cases sign <;> simp [ErrorSign.epsilon]
  have ha1 : 1 < a := by linarith [hH.beta_gt_one]
  have hTcont : ContinuousOn (H.T sign) (Icc a b) :=
    (hH.continuous sign).mono (by
      intro x hx
      exact (zero_lt_one.trans ha1).trans_le hx.1)
  have hfcont : ContinuousOn f (Icc a b) := by
    exact ((continuousOn_id.pow 2).mul hTcont).neg
  have hgcont : ContinuousOn g (Icc a b) := by
    apply continuousOn_id.mul
    exact (hH.continuous sign.opposite).comp
      (continuousOn_id.sub continuousOn_const) (by
        intro x hx
        exact sub_pos.mpr (ha1.trans_le hx.1))
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x := by
    intro x hx
    simpa [f, g, hatTailIntegrand, neg_mul] using
      (hH.dde sign x (lt_of_le_of_lt ha hx.1)).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hfcont hderiv (hgcont.intervalIntegrable_of_Icc hab)
  change (∫ t in a..b, g t) = _
  rw [hFTC]
  change -weightedHat H sign b - (-weightedHat H sign a) = _
  ring

/-- Exact κ=1 finite weighted-tail bound required by Claim 14.6(iii).
It holds on the full source range `β + ε_sign ≤ s ≤ σ`.  The source's κ=1
condition `0 < θ` is more than needed here: `0 ≤ θ` suffices because truncation
at finite `σ` leaves the strictly positive value `weightedHat H sign σ`.
The degenerate endpoint `s = σ` is split off explicitly. -/
theorem lemma13_3_weightedTail_strict_closedRange
    {H : Section13HatLayers} {β θ s σ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hθ : 0 ≤ θ) (hs : β + sign.epsilon ≤ s) (hsσ : s ≤ σ) :
    (∫ t in s..σ, ((t - 1) / t) ^ θ * hatTailIntegrand H sign t) <
      weightedHat H sign s := by
  have heps : 0 ≤ sign.epsilon := by
    cases sign <;> simp [ErrorSign.epsilon]
  have hs1 : 1 < s := by linarith [hH.beta_gt_one]
  have hs0 : 0 < s := zero_lt_one.trans hs1
  have hWs : 0 < weightedHat H sign s :=
    mul_pos (sq_pos_of_pos hs0) (hH.positive sign s hs0)
  rcases hsσ.eq_or_lt with rfl | hsσlt
  · simpa using hWs
  · have hσ1 : 1 < σ := hs1.trans hsσlt
    have hWσ : 0 < weightedHat H sign σ := by
      have hσ0 : 0 < σ := zero_lt_one.trans hσ1
      exact mul_pos (sq_pos_of_pos hσ0) (hH.positive sign σ hσ0)
    have htailcont : ContinuousOn (hatTailIntegrand H sign) (Icc s σ) := by
      apply continuousOn_id.mul
      exact (hH.continuous sign.opposite).comp
        (continuousOn_id.sub continuousOn_const) (by
          intro t ht
          exact sub_pos.mpr (hs1.trans_le ht.1))
    have hratio : ContinuousOn (fun t : ℝ => (t - 1) / t) (Icc s σ) :=
      (continuousOn_id.sub continuousOn_const).div continuousOn_id (by
        intro t ht
        exact ne_of_gt (hs0.trans_le ht.1))
    have hweightcont : ContinuousOn (fun t : ℝ => ((t - 1) / t) ^ θ) (Icc s σ) := by
      apply hratio.rpow continuousOn_const
      intro t ht
      left
      exact ne_of_gt (div_pos (sub_pos.mpr (hs1.trans_le ht.1))
        (hs0.trans_le ht.1))
    have hweightedcont : ContinuousOn
        (fun t : ℝ => ((t - 1) / t) ^ θ * hatTailIntegrand H sign t)
        (Icc s σ) := hweightcont.mul htailcont
    have hpoint : ∀ t ∈ Icc s σ,
        ((t - 1) / t) ^ θ * hatTailIntegrand H sign t ≤
          hatTailIntegrand H sign t := by
      intro t ht
      have ht1 : 1 < t := hs1.trans_le ht.1
      have ht0 : 0 < t := zero_lt_one.trans ht1
      have hbase0 : 0 ≤ (t - 1) / t := (div_pos (sub_pos.mpr ht1) ht0).le
      have hbase1 : (t - 1) / t ≤ 1 := (div_le_one ht0).2 (by linarith)
      have hw1 : ((t - 1) / t) ^ θ ≤ 1 := Real.rpow_le_one hbase0 hbase1 hθ
      have htail0 : 0 ≤ hatTailIntegrand H sign t :=
        (mul_pos ht0 (hH.positive sign.opposite (t - 1) (sub_pos.mpr ht1))).le
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 htail0
    have hmono :
        (∫ t in s..σ, ((t - 1) / t) ^ θ * hatTailIntegrand H sign t) ≤
          ∫ t in s..σ, hatTailIntegrand H sign t :=
      intervalIntegral.integral_mono_on hsσ
        (hweightedcont.intervalIntegrable_of_Icc hsσ)
        (htailcont.intervalIntegrable_of_Icc hsσ) hpoint
    have hfinite := integral_hatTailIntegrand_closedThreshold hH sign hs hsσ
    have hunweighted :
        (∫ t in s..σ, hatTailIntegrand H sign t) < weightedHat H sign s := by
      rw [hfinite]
      linarith
    exact hmono.trans_lt hunweighted


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
