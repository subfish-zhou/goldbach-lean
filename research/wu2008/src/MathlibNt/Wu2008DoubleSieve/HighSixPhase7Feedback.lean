import MathlibNt.Wu2008DoubleSieve.HighSixPhase5Positive
import MathlibNt.Wu2008DoubleSieve.ImprovementCrossLower

namespace Wu2008DoubleSieve.HighSixPhase7
open Real Set MeasureTheory
noncomputable section

/-- The natural fixed-delta remainder, without discarding the original penalty. -/
def seed : ℝ := 4193986163027492227/1772569457627151690000

theorem seed_pos : 0 < seed := by norm_num [seed]

theorem psi_delta_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    seed ≤ firstFunctionalGainPsi δ (13/5) (179/50) := by
  rw [firstFunctionalGainPsi_eq_source_sub_penalty (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  have hd : 0 ≤ 2*δ/(1-2*δ) := div_nonneg (by linarith) (by linarith)
  have hdhi : 2*δ/(1-2*δ) ≤ 1/49 := (div_le_iff₀ (by linarith)).2 (by linarith)
  have hp : (2*δ/(1-2*δ))*omega3XIntegralEnvelope (13/5) (179/50) ≤
      (1/49 : ℝ)*(9563183/659100000) := by
    calc
      _ ≤ (2*δ/(1-2*δ))*(9563183/659100000) :=
        mul_le_mul_of_nonneg_left HighSixPhase5.envelope_upper hd
      _ ≤ _ := mul_le_mul_of_nonneg_right hdhi (by norm_num)
  dsimp [seed]
  linarith only [HighSixPhase5.psi_lower,hp]

/-- The first functional inequality feeds the actual H, at fixed delta. -/
theorem H_seed {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    seed ≤ wuImprovementLimit true δ (13/5) := by
  have hfirst := wuImprovementLimit_firstFunctionalGain
    (s := (13/5 : ℝ)) (t := (179/50 : ℝ)) hδ (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hH := wuImprovementLimit_nonneg true hδ (by linarith : δ < 1/2)
    (s := (179/50 : ℝ)) (by norm_num) (by norm_num)
  have hi : 0 ≤ ∫ u in (1-1/(13/5) : ℝ)..(1-1/(179/50)),
      wuImprovementLimit false δ ((179/50)*u)/(u*(1-u)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    have hu0 : 0 ≤ u := by norm_num at hu; linarith [hu.1]
    have hu1 : 0 ≤ 1-u := by norm_num at hu; linarith [hu.2]
    apply div_nonneg _ (mul_nonneg hu0 hu1)
    apply wuImprovementLimit_nonneg false hδ (by linarith)
    · norm_num at hu; linarith [hu.1]
    · norm_num at hu; linarith [hu.2]
  linarith only [psi_delta_lower hδ hδhi,hfirst,hH,hi]

/-- A positive-length interval is propagated through the literal lower cross integral. -/
theorem h_seven_halves {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    seed/26 ≤ wuImprovementLimit false δ (7/2) := by
  have hcross := wuImprovementLimit_lower_cross (s := (7/2 : ℝ)) (t := (18/5 : ℝ))
    hδ (by linarith) (by norm_num) (by norm_num) (by norm_num)
  norm_num only at hcross
  have hnonneg := wuImprovementLimit_nonneg false hδ (by linarith : δ < 1/2)
    (s := (18/5 : ℝ)) (by norm_num) (by norm_num)
  have hi : seed/26 ≤ ∫ u in (5/2 : ℝ)..(13/5), wuImprovementLimit true δ u/u := by
    have hm : (∫ u in (5/2 : ℝ)..(13/5), seed*(5/13)) ≤
        ∫ u in (5/2 : ℝ)..(13/5), wuImprovementLimit true δ u/u := by
      apply intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
        (wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
          (by norm_num) (by norm_num) (by norm_num))
      intro u hu
      have hseed := (H_seed hδ hδhi).trans
        (wuImprovementLimit_upper_antitone hδ (by linarith)
          ⟨by linarith [hu.1],by linarith [hu.2]⟩ ⟨by norm_num,by norm_num⟩ hu.2)
      apply (le_div_iff₀ (by linarith [hu.1])).2
      have hh := mul_le_mul_of_nonneg_left hu.2 seed_pos.le
      nlinarith only [hseed,hh]
    rw [intervalIntegral.integral_const,smul_eq_mul] at hm
    linarith only [hm]
  linarith only [hcross,hnonneg,hi]

/-- Lower-side monotonicity is derived from cross and nonnegativity, not assumed. -/
theorem h_lower_on {δ u : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hu : u ∈ Icc (3 : ℝ) (7/2)) : seed/26 ≤ wuImprovementLimit false δ u := by
  have hc := wuImprovementLimit_lower_cross (s := u) (t := (7/2 : ℝ))
    hδ (by linarith) (by linarith [hu.1]) hu.2 (by norm_num)
  have hi : 0 ≤ ∫ v in (u-1)..(7/2-1 : ℝ), wuImprovementLimit true δ v/v := by
    apply intervalIntegral.integral_nonneg (by linarith [hu.2])
    intro v hv
    exact div_nonneg (wuImprovementLimit_nonneg true hδ (by linarith)
      (by linarith [hu.1,hv.1]) (by linarith [hv.2])) (by linarith [hu.1,hv.1])
  linarith only [hc,hi,h_seven_halves hδ hδhi]

/-- The second cross step reaches H(4), beyond the original short seed interval. -/
theorem H_four {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    seed/182 ≤ wuImprovementLimit true δ 4 := by
  have hc := wuImprovementLimit_upper_cross (s := (4 : ℝ)) (t := (9/2 : ℝ))
    hδ (by linarith) (by norm_num) (by norm_num) (by norm_num)
  norm_num only at hc
  have hnonneg := wuImprovementLimit_nonneg true hδ (by linarith : δ < 1/2)
    (s := (9/2 : ℝ)) (by norm_num) (by norm_num)
  have hi : seed/182 ≤ ∫ u in (3 : ℝ)..(7/2), wuImprovementLimit false δ u/u := by
    have hm : (∫ u in (3 : ℝ)..(7/2), (seed/26)*(2/7)) ≤
        ∫ u in (3 : ℝ)..(7/2), wuImprovementLimit false δ u/u := by
      apply intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
        (wuImprovementLimit_div_intervalIntegrable false hδ (by linarith)
          (by norm_num) (by norm_num) (by norm_num))
      intro u hu
      apply (le_div_iff₀ (by linarith [hu.1])).2
      have hs := h_lower_on hδ hδhi hu
      have hh := mul_le_mul_of_nonneg_left hu.2 seed_pos.le
      nlinarith only [hs,hh]
    rw [intervalIntegral.integral_const,smul_eq_mul] at hm
    linarith only [hm]
  linarith only [hc,hnonneg,hi]

end
end Wu2008DoubleSieve.HighSixPhase7
