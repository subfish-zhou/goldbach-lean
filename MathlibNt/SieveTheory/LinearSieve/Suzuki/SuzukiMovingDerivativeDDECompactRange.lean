import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146Quantitative

open Set Filter Topology
open scoped Classical

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The pointwise DDE allowance divided by the positive weighted hat layer. -/
noncomputable def compactDerivativeRatio
    (H : Section13HatLayers) (sign : ErrorSign) (t : ℝ) : ℝ :=
  (t * H.T sign.opposite (t - 1)) / weightedHat H sign t

lemma compactDerivativeRatio_continuousOn
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) (M : ℝ) :
    ContinuousOn (compactDerivativeRatio H sign) (Icc 2 M) := by
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have htm0 : 0 < t - 1 := by linarith [ht.1]
  have hTt : ContinuousAt (H.T sign) t :=
    (hH.continuous sign).continuousAt (Ioi_mem_nhds ht0)
  have hTop : ContinuousAt (H.T sign.opposite) (t - 1) :=
    (hH.continuous sign.opposite).continuousAt (Ioi_mem_nhds htm0)
  have hshift : ContinuousAt (fun x : ℝ => H.T sign.opposite (x - 1)) t :=
    hTop.comp_of_eq (continuousAt_id.sub continuousAt_const) rfl
  have hnum : ContinuousAt (fun x : ℝ => x * H.T sign.opposite (x - 1)) t :=
    continuousAt_id.mul hshift
  have hden : ContinuousAt (weightedHat H sign) t := by
    change ContinuousAt (fun x : ℝ => x ^ 2 * H.T sign x) t
    exact (continuousAt_id.pow 2).mul hTt
  have hden_ne : weightedHat H sign t ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt ht0))
      (ne_of_gt (hH.positive sign t ht0))
  exact (hnum.div hden hden_ne).continuousWithinAt

lemma compactDerivativeRatio_pos
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {t : ℝ} (ht : 2 ≤ t) :
    0 < compactDerivativeRatio H sign t := by
  have ht0 : 0 < t := by linarith
  have htm0 : 0 < t - 1 := by linarith
  apply div_pos
  · exact mul_pos ht0 (hH.positive sign.opposite (t - 1) htm0)
  · dsimp [weightedHat]
    exact mul_pos (sq_pos_of_pos ht0) (hH.positive sign t ht0)

/-- On a fixed compact head, the two DDE/weighted-hat ratios admit common
strictly positive lower and finite upper bounds.  Both bounds are independent
of the sign, of `ε ∈ {0,1}`, and of the point in the head. -/
theorem exists_compactDerivativeRatio_bounds
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {M : ℝ} (hM : 3 ≤ M) :
    ∃ m B : ℝ, 0 < m ∧
      ∀ (sign : ErrorSign) (t : ℝ), t ∈ Icc 2 M →
        m ≤ compactDerivativeRatio H sign t ∧
          compactDerivativeRatio H sign t ≤ B := by
  have hne : (Icc (2 : ℝ) M).Nonempty := nonempty_Icc.mpr (by linarith)
  obtain ⟨tp, htp, hpmin⟩ := isCompact_Icc.exists_isMinOn hne
    (compactDerivativeRatio_continuousOn hH ErrorSign.plus M)
  obtain ⟨tm, htm, hmmin⟩ := isCompact_Icc.exists_isMinOn hne
    (compactDerivativeRatio_continuousOn hH ErrorSign.minus M)
  obtain ⟨up, hup, hpmax⟩ := isCompact_Icc.exists_isMaxOn hne
    (compactDerivativeRatio_continuousOn hH ErrorSign.plus M)
  obtain ⟨um, hum, hmmax⟩ := isCompact_Icc.exists_isMaxOn hne
    (compactDerivativeRatio_continuousOn hH ErrorSign.minus M)
  let m := min (compactDerivativeRatio H ErrorSign.plus tp)
    (compactDerivativeRatio H ErrorSign.minus tm)
  let B := max (compactDerivativeRatio H ErrorSign.plus up)
    (compactDerivativeRatio H ErrorSign.minus um)
  have hmpos : 0 < m := lt_min
    (compactDerivativeRatio_pos hH ErrorSign.plus htp.1)
    (compactDerivativeRatio_pos hH ErrorSign.minus htm.1)
  refine ⟨m, B, hmpos, ?_⟩
  intro sign t ht
  cases sign with
  | plus =>
      exact ⟨(min_le_left _ _).trans (hpmin ht),
        (hpmax ht).trans (le_max_left _ _)⟩
  | minus =>
      exact ⟨(min_le_right _ _).trans (hmmin ht),
        (hmmax ht).trans (le_max_right _ _)⟩

/-- Claim 14.6(i), compact-head part: after one threshold depending only on the
fixed endpoint `M` (and on `H,d`), the exact derivative domination holds
uniformly for both signs, both shifts `ε = 0,1`, and every
`2 + sign.epsilon < t ≤ M`.  No certificate assumption is used. -/
theorem eventually_derivativeDDE_domination_on_compactRange
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {d M : ℝ} (hd : 0 ≤ d) (hM : 3 ≤ M) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      ∀ (sign : ErrorSign) (ε t : ℝ),
        (ε = 0 ∨ ε = 1) → 2 + sign.epsilon < t → t ≤ M →
        weightedHat H sign t * perturbationSlope D d ε t ≤
          t * H.T sign.opposite (t - 1) := by
  obtain ⟨m, B, hm, hrange⟩ := exists_compactDerivativeRatio_bounds hH hM
  let C : ℝ := (1 + M * d) * (M + 1) ^ d
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)
  let X : ℝ := max 1 (C / m)
  let D₀ : ℝ := Real.exp X
  have hX : 0 < X := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hD₀ : 1 < D₀ := by
    dsimp [D₀]
    exact Real.one_lt_exp_iff.mpr hX
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD sign ε t hε ht hMt
  have hD1 : 1 < D := hD₀.trans_le hD
  have hlog : 0 < Real.log D := Real.log_pos hD1
  have hXD : X ≤ Real.log D := by
    apply (Real.le_log_iff_exp_le (zero_lt_one.trans hD1)).2
    simpa [D₀] using hD
  have hCm : C / m ≤ Real.log D := (le_max_right _ _).trans hXD
  have hCle : C ≤ m * Real.log D := by
    simpa [mul_comm] using (div_le_iff₀ hm).mp hCm
  have hslope : perturbationSlope D d ε t ≤ m := by
    have hε0 : 0 ≤ ε := by rcases hε with rfl | rfl <;> norm_num
    have hε1 : ε ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
    have ht1 : 1 ≤ t := by
      cases sign <;> simp [ErrorSign.epsilon] at ht <;> linarith
    have hs := perturbationSlope_le hlog hd ht1 hMt hε0 hε1
    have hfrac : C / Real.log D ≤ m := (div_le_iff₀ hlog).2 (by
      simpa [mul_comm] using hCle)
    exact hs.trans (by simpa [C] using hfrac)
  have ht2 : 2 ≤ t := by
    cases sign <;> simp [ErrorSign.epsilon] at ht <;> linarith
  have hratio := (hrange sign t ⟨ht2, hMt⟩).1
  have hsratio : perturbationSlope D d ε t ≤
      compactDerivativeRatio H sign t := hslope.trans hratio
  have ht0 : 0 < t := by linarith
  have hWpos : 0 < weightedHat H sign t := by
    dsimp [weightedHat]
    exact mul_pos (sq_pos_of_pos ht0) (hH.positive sign t ht0)
  calc
    weightedHat H sign t * perturbationSlope D d ε t ≤
        weightedHat H sign t * compactDerivativeRatio H sign t :=
      mul_le_mul_of_nonneg_left hsratio hWpos.le
    _ = t * H.T sign.opposite (t - 1) := by
      dsimp [compactDerivativeRatio]
      field_simp [ne_of_gt hWpos]


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
