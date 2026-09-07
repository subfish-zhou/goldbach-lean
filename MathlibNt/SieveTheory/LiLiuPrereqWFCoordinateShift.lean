import MathlibNt.SieveTheory.JurkatRichert1965ChenDelayMonotonicity

/-!
# Uniform changes of sieve coordinate

The actual delay equations give a derivative bound of order `1 / s` on
`[s, ∞)`. Thus multiplicative coordinate changes have a bound independent of
the (unbounded) coordinate. The endpoint `s = 2` needs only continuity.
-/

noncomputable section

open Set
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.CoordinateShift

theorem delayConstant_pos : 0 < jr1965DelayConstant := by
  unfold jr1965DelayConstant
  positivity

/-- The upper function changes at most by the delay constant times relative length. -/
theorem upper_sub_le_relative_length {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    jr1965F s - jr1965F t ≤ jr1965DelayConstant / s * (t - s) := by
  have hbound (u : ℝ) (hu : u ∈ interior (Icc s t)) :
      -(jr1965DelayConstant / s) ≤ deriv jr1965F u := by
    rw [interior_Icc] at hu
    have hu2 : 2 < u := lt_of_le_of_lt hs hu.1
    have hs0 : 0 < s := by linarith
    have hu0 : 0 < u := by linarith
    rw [(hasDerivAt_jr1965F hu2).deriv]
    have hnum : -jr1965DelayConstant ≤ jr1965f (u - 1) - jr1965F u := by
      have := jr1965f_nonneg (show 0 < u - 1 by linarith)
      have := jr1965F_le_delayConstant (show 1 ≤ u by linarith)
      linarith
    have hdiv := div_le_div_of_nonneg_left delayConstant_pos.le hs0 hu.1.le
    have hnumdiv := div_le_div_of_nonneg_right hnum hu0.le
    rw [neg_div] at hnumdiv
    linarith
  have h := (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv
    (continuousOn_jr1965F.mono (fun u hu => by
      change (0 : ℝ) < u
      linarith [hu.1]))
    (fun u hu => (hasDerivAt_jr1965F (by
      rw [interior_Icc] at hu
      linarith [hu.1])).differentiableAt.differentiableWithinAt)
    hbound s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
  linarith

/-- The lower function obeys the same relative-length estimate. -/
theorem lower_sub_le_relative_length {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    jr1965f t - jr1965f s ≤ jr1965DelayConstant / s * (t - s) := by
  have hbound (u : ℝ) (hu : u ∈ interior (Icc s t)) :
      deriv jr1965f u ≤ jr1965DelayConstant / s := by
    rw [interior_Icc] at hu
    have hu2 : 2 < u := lt_of_le_of_lt hs hu.1
    rw [(hasDerivAt_jr1965f hu2).deriv]
    have hnum : jr1965F (u - 1) - jr1965f u ≤ jr1965DelayConstant := by
      have := jr1965f_nonneg (show 0 < u by linarith)
      have := jr1965F_le_delayConstant (show 1 ≤ u - 1 by linarith)
      linarith
    exact (div_le_div_of_nonneg_right hnum (by linarith)).trans
      (div_le_div_of_nonneg_left delayConstant_pos.le (by linarith) hu.1.le)
  exact (convex_Icc s t).image_sub_le_mul_sub_of_deriv_le
    (continuousOn_jr1965f.mono (fun u hu => by
      change (0 : ℝ) < u
      linarith [hu.1]))
    (fun u hu => (hasDerivAt_jr1965f (by
      rw [interior_Icc] at hu
      linarith [hu.1])).differentiableAt.differentiableWithinAt)
    hbound s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst

theorem scale_bounds {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    1 ≤ 1 + ε + ε ^ 9 ∧
      1 + ε + ε ^ 9 ≤ 1 + 2 * ε ∧ 2 * (1 + ε + ε ^ 9) < 3 := by
  have hp0 : 0 ≤ ε ^ 9 := pow_nonneg hε.le 9
  have hp8 : ε ^ 8 ≤ 1 := pow_le_one₀ hε.le (by linarith)
  have hp9 : ε ^ 9 ≤ ε := by
    calc
      ε ^ 9 = ε * ε ^ 8 := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hp8 hε.le
      _ = ε := mul_one _
  constructor
  · linarith
  constructor <;> linarith

/-- Both absolute shifts are uniform over the entire source range `s ≥ 2`. -/
theorem abs_shifts_le {ε s : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) (hs : 2 ≤ s) :
    |jr1965F s - jr1965F ((1 + ε + ε ^ 9) * s)| ≤
        (2 * jr1965DelayConstant) * ε ∧
      |jr1965f ((1 + ε + ε ^ 9) * s) - jr1965f s| ≤
        (2 * jr1965DelayConstant) * ε := by
  have hc := scale_bounds hε hε8
  have hs0 : 0 < s := by linarith
  have hst : s ≤ (1 + ε + ε ^ 9) * s := by nlinarith [hc.1]
  have ht0 : 0 < (1 + ε + ε ^ 9) * s := hs0.trans_le hst
  have hbudget :
      jr1965DelayConstant / s * ((1 + ε + ε ^ 9) * s - s) ≤
        (2 * jr1965DelayConstant) * ε := by
    calc
      _ = jr1965DelayConstant * ((1 + ε + ε ^ 9) - 1) := by
        field_simp
      _ ≤ (2 * jr1965DelayConstant) * ε := by
        nlinarith [mul_le_mul_of_nonneg_left hc.2.1 delayConstant_pos.le]
  constructor
  · rw [abs_of_nonneg (sub_nonneg.mpr (antitoneOn_jr1965F hs0 ht0 hst))]
    exact (upper_sub_le_relative_length hs hst).trans hbudget
  · rw [abs_of_nonneg (sub_nonneg.mpr (monotoneOn_jr1965f hs0 ht0 hst))]
    exact (lower_sub_le_relative_length hs hst).trans hbudget

theorem exists_uniform_coordinate_shift :
    ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε < 1 / 8 → ∀ s : ℝ, 2 ≤ s →
      jr1965F s ≤ jr1965F ((1 + ε + ε ^ 9) * s) + C * ε ∧
        jr1965f ((1 + ε + ε ^ 9) * s) ≤ jr1965f s + C * ε := by
  refine ⟨2 * jr1965DelayConstant, mul_pos (by norm_num) delayConstant_pos, ?_⟩
  intro ε hε hε8 s hs
  obtain ⟨hF, hf⟩ := abs_shifts_le hε hε8 hs
  exact ⟨by linarith [(le_abs_self _).trans hF],
    by linarith [(le_abs_self _).trans hf]⟩

theorem lower_edge_le {ε sQ : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8)
    (hsQ : 2 ≤ sQ) (hsQc : sQ ≤ 2 * (1 + ε + ε ^ 9)) :
    jr1965f sQ ≤ (2 * jr1965DelayConstant) * ε := by
  have h := lower_sub_le_relative_length (s := 2) le_rfl hsQ
  rw [jr1965f_initial (u := 2) (by norm_num), sub_zero] at h
  have hc := (scale_bounds hε hε8).2.1
  calc
    jr1965f sQ ≤ jr1965DelayConstant / 2 * (sQ - 2) := h
    _ ≤ (2 * jr1965DelayConstant) * ε := by
      nlinarith [mul_le_mul_of_nonneg_left
        (show sQ - 2 ≤ 4 * ε by linarith) delayConstant_pos.le]

/-- Exact cancellation of the edge upper main term against the logarithm ratio. -/
theorem upper_edge_exact {c sQ : ℝ} (_hsQ : 2 ≤ sQ)
    (hsQc : sQ ≤ 2 * c) (hc3 : 2 * c < 3) :
    jr1965F 2 * (2 * c / sQ) = jr1965F sQ * c := by
  rw [jr1965F_eq_of_le_three (by norm_num),
    jr1965F_eq_of_le_three (by linarith)]
  ring

theorem upper_edge_exact_epsilon {ε sQ : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8)
    (hsQ : 2 ≤ sQ) (hsQc : sQ ≤ 2 * (1 + ε + ε ^ 9)) :
    jr1965F 2 * (2 * (1 + ε + ε ^ 9) / sQ) =
      jr1965F sQ * (1 + ε + ε ^ 9) :=
  upper_edge_exact hsQ hsQc (scale_bounds hε hε8).2.2

end MathlibNt.SieveTheory.LiLiuPrereqWF.CoordinateShift
