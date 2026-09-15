import MathlibNt.Wu2008DoubleSieve.WuSourceLevel
import MathlibNt.Wu2008DoubleSieve.BoxMassTheta

/-!
# A genuine relative signed remainder on Wu's actual boxes

The proved ordinary BV estimate is used at exponent `5*k+3`, while
the actual Theta lower bound has exponent `5*k+2`. The remaining
inverse logarithm absorbs every fixed finite family length. No
positivity, mass estimate, or distribution bound is assumed.
-/

namespace Wu2008DoubleSieve

open Finset Filter
open scoped Classical Topology

/-- The threshold precedes every box, sign, cutoff and admissible level.
The family length is fixed before that threshold, not silently uniform. -/
theorem wu_signed_rosser_remainder_relative (k L : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + Real.log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * Real.log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
          ∀ upper : Fin L → Bool, ∀ D : Fin L → ℕ → ℕ, ∀ z : Fin L → ℕ → ℝ,
          (∀ l, ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
            D l d ≤ convolutionModulusCutoff N δ / d + 1) →
          |∑ l, convolutionRosserRemainder N (convolutionWuWindows N Δ V)
            (upper l) (D l) (z l)| ≤
              ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
                (convolutionWuWindows N Δ V) := by
  obtain ⟨C, hC, N1, hBV⟩ := wu_signed_rosser_bombieri_vinogradov k L hδ
    (show (0 : ℝ) < (5 * k + 3 : ℕ) by positivity)
  obtain ⟨c, hc, N2, hTheta⟩ := wu_boxTheta_lower k hδ hδhi
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop N1, eventually_ge_atTop N2,
    eventually_ge_atTop (2 : ℕ),
    hlogTop.eventually (eventually_ge_atTop ((L : ℝ) * C / (ε * c)))]
      with N hN1 hN2 hN hlogBudget
  intro i hik Δ hlo hhi V hV hprefix upper D z hD
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hB := hBV N hN1 i hik Δ hlo hhi V hV upper D z hD
  rw [Real.rpow_natCast] at hB
  have hT := hTheta N hN2 i hik Δ hlo hhi V hV hprefix
  have hbudget : (L : ℝ) * C / Real.log N ≤ ε * c := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hc)).mp hlogBudget
    nlinarith
  calc
    _ ≤ (L : ℝ) * (C * N / Real.log N ^ (5 * k + 3)) := hB
    _ = ((L : ℝ) * C / Real.log N) *
        ((N : ℝ) / Real.log N ^ (5 * k + 2)) := by
      rw [show 5 * k + 3 = (5 * k + 2) + 1 by omega, pow_succ]
      ring
    _ ≤ (ε * c) * ((N : ℝ) / Real.log N ^ (5 * k + 2)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = ε * (c * (N : ℝ) / Real.log N ^ (5 * k + 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hT hε.le

/-- Relative payment at the actual common level, with its support
restriction discharged from the literal source boxes. -/
theorem wu_common_level_remainder_relative (k L : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + Real.log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * Real.log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
          ∀ upper : Fin L → Bool, ∀ z : Fin L → ℕ → ℝ,
          |∑ l, convolutionRosserRemainder N (convolutionWuWindows N Δ V)
            (upper l) (fun _ => wuCommonRosserLevel N δ V) (z l)| ≤
              ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
                (convolutionWuWindows N Δ V) := by
  obtain ⟨N0, h⟩ := wu_signed_rosser_remainder_relative k L hδ hδhi hε
  refine ⟨N0, ?_⟩
  intro N hN i hik Δ hlo hhi V hV hprefix upper z
  apply h N hN i hik Δ hlo hhi V hV hprefix upper
  intro _l d hd
  exact wuCommonRosserLevel_le_combined hd

end Wu2008DoubleSieve
