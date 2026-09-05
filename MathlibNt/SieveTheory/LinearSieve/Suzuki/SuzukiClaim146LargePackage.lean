import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146ShortInterval

open Set Filter Topology
namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Claims 14.6(i) and (ii), simultaneously and with no externally supplied
margin: under the source range condition `-1 < Δ`, both conclusions hold for
all sufficiently large `D`. -/
theorem claim14_6_i_ii_for_sufficiently_large_D
    {H : Section13HatLayers} {β d Δ σ : ℝ}
    (hH : Section13HatContract H β) (hd : 0 ≤ d) (hΔ : -1 < Δ)
    (hσ : ∀ sign : ErrorSign, β + sign.epsilon ≤ σ) :
    ∃ D₀, 1 < D₀ ∧ ∀ D, D₀ ≤ D →
      (∀ sign ε, ε = 0 ∨ ε = 1 →
        AntitoneOn (lambda H sign D d ε) (Icc (β + sign.epsilon) σ)) ∧
      Claim14_6_MonotoneQPremise H D d Δ σ := by
  obtain ⟨ρdelay, hρdelay, hdelay⟩ := exists_common_delayRatioMargin hH hσ
  have hσgt : 1 < σ := by
    have hm := hσ ErrorSign.minus
    simp [ErrorSign.epsilon] at hm
    linarith [hH.beta_gt_one]
  have hσσ : 0 < σ * (σ - 1) := mul_pos (zero_lt_one.trans hσgt) (sub_pos.mpr hσgt)
  have hΔpos : 0 < 1 + Δ := by linarith
  let ρ : ℝ := min ρdelay ((1 + Δ) / (σ * (σ - 1)))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hρdelay (div_pos hΔpos hσσ)
  have hρle : ρ ≤ ρdelay := by
    dsimp [ρ]
    exact min_le_left _ _
  have hdelay' : ∀ sign t, β + sign.epsilon < t → t ≤ σ →
      ρ * weightedHat H sign t ≤ t * H.T sign.opposite (t - 1) := by
    intro sign t htl htu
    have htpos : 0 < t := by
      have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
      linarith [hH.beta_gt_one, htl]
    have hW0 : 0 ≤ weightedHat H sign t :=
      mul_nonneg (sq_nonneg t) (hH.positive sign t htpos).le
    exact (mul_le_mul_of_nonneg_right hρle hW0).trans (hdelay sign t htl htu)
  have hshort : ρ * (σ * (σ - 1)) ≤ 1 + Δ := by
    have hr : ρ ≤ (1 + Δ) / (σ * (σ - 1)) := by
      dsimp [ρ]
      exact min_le_right _ _
    exact (le_div_iff₀ hσσ).mp hr
  let C : ℝ := (1 + σ * d) * (σ + 1) ^ d
  have hC0 : 0 ≤ C := by
    dsimp [C]
    apply mul_nonneg
    · nlinarith [hσgt]
    · exact Real.rpow_nonneg (by linarith [hσgt]) _
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
  have hDlarge : (1 + σ * d) * (σ + 1) ^ d ≤ ρ * Real.log D := by
    simpa only [C] using hCx.trans (mul_le_mul_of_nonneg_left hlogx hρ.le)
  constructor
  · exact claim14_6_i_of_log_bound hH hd hσ hρ hlog hDlarge hdelay'
  · exact claim14_6_ii_of_log_bound hH hd hΔ.le hσ hρ hlog hDlarge hdelay' hshort


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
