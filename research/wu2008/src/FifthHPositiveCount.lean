import FifthHPositive
import FifthHEndpoint
import MathlibNt.Wu2008DoubleSieve.FifthPairEndpoint

namespace Wu2008DoubleSieve
open Set Real Filter MeasureTheory
open scoped Classical Topology

/-- Only the classical term varies continuously with delta; h has no delta regularity premise. -/
theorem fifthH_improved_delta_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 1000 ∧
      fifthPairFlin + fifthHGain - ε ≤ fifthHFdelta δ - ε / 2 := by
  obtain ⟨δ, hδ, hδhi, hclose⟩ := fifthPair_Fdelta_close (half_pos hε)
  refine ⟨δ, hδ, hδhi, ?_⟩
  have hc := (abs_lt.mp hclose).1
  have hg := fifthH_Fdelta_uniform_gain hδ hδhi
  linarith

/-- Full unrounded gain family for both actual cutoffs, with delta fixed before the common T. -/
theorem fifthH_actual_improved_both {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin + fifthHGain - ε) * truncatedSixthMassScale N ≤
        (fifthPairCount N : ℝ) ∧
      (fifthPairFlin + fifthHGain - ε) * truncatedSixthMassScale N ≤
        (fifthHClosedCount N : ℝ) := by
  obtain ⟨δ, hδ, hδhi, hcoeff⟩ := fifthH_improved_delta_payment hε
  obtain ⟨Ts, hTs, hs⟩ := fifthH_actual_Fdelta_lower hδ hδhi (half_pos hε)
  obtain ⟨Tc, hTc, hc⟩ := fifthH_actual_closed_Fdelta_lower hδ hδhi (half_pos hε)
  refine ⟨max Ts Tc, hTs.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hNs := (le_max_left Ts Tc).trans hN
  have hNc := (le_max_right Ts Tc).trans hN
  have hm := mul_le_mul_of_nonneg_right hcoeff
    (truncatedSixthClosure_scale_nonneg (hTs.trans hNs))
  exact ⟨hm.trans (hs N hNs he), hm.trans (hc N hNc he)⟩

/-- Source normalization and unchanged ordered prime-pair count, at the strict cutoff. -/
theorem fifthH_actual_improved_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin + fifthHGain - ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        (fifthPairCount N : ℝ) := by
  obtain ⟨T, hT, h⟩ := fifthH_actual_improved_both hε
  refine ⟨T, hT, fun N hN he => ?_⟩
  simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using (h N hN he).1

/-- The same unrounded gain survives the independently paid actual closed endpoint. -/
theorem fifthH_actual_closed_improved_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin + fifthHGain - ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        (fifthHClosedCount N : ℝ) := by
  obtain ⟨T, hT, h⟩ := fifthH_actual_improved_both hε
  refine ⟨T, hT, fun N hN he => ?_⟩
  simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using (h N hN he).2

/-- Every strictly smaller gain is paid in full, not just a preselected half-gain. -/
theorem fifthH_actual_paid_both {g : ℝ} (hg : g < fifthHGain) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin + g) * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        (fifthPairCount N : ℝ) ∧
      (fifthPairFlin + g) * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        (fifthHClosedCount N : ℝ) := by
  obtain ⟨T, hT, h⟩ := fifthH_actual_improved_both (sub_pos.mpr hg)
  refine ⟨T, hT, fun N hN he => ?_⟩
  have hm := h N hN he
  have heq : fifthPairFlin + fifthHGain - (fifthHGain - g) = fifthPairFlin + g := by ring
  rw [heq] at hm
  simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hm

/-- One fixed strictly improved coefficient; the full gain family above remains available. -/
noncomputable def fifthHImprovedCoefficient : ℝ := fifthPairFlin + fifthHGain / 2

theorem fifthH_improved_coefficient_strict : fifthPairFlin < fifthHImprovedCoefficient := by
  unfold fifthHImprovedCoefficient
  exact lt_add_of_pos_right _ (half_pos fifthHGain_pos)

/-- A hypothesis-free actual counting improvement, after paying a positive delta/error budget. -/
theorem fifthH_actual_fixed_improved_both :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      fifthHImprovedCoefficient * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        (fifthPairCount N : ℝ) ∧
      fifthHImprovedCoefficient * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        (fifthHClosedCount N : ℝ) :=
  fifthH_actual_paid_both (half_lt_self fifthHGain_pos)

end Wu2008DoubleSieve
