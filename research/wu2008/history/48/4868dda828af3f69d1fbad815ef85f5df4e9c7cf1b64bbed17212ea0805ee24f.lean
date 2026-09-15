import MathlibNt.Wu2008DoubleSieve.TableGainLower

/-!
# The actual nine-coordinate lower-gain map

All coefficients are nonnegative literal source integrals and logarithms.
They are independent of delta; no numerical seed certificate is presumed.
-/

namespace Wu2008DoubleSieve

open Real
open scoped BigOperators Matrix

noncomputable def tableGainB (s : ℝ) (j : Fin 9) : ℝ :=
  ∑ i : Fin 29, tableGainWeight s i * tableGainE i j

theorem tableGainB_nonneg (s : ℝ) (j : Fin 9) : 0 ≤ tableGainB s j :=
  Finset.sum_nonneg (fun i _ =>
    mul_nonneg (tableGainWeight_nonneg s i) (tableGainE_nonneg i j))

theorem tableGainB_composition (s : ℝ) (X : Fin 9 → ℝ) :
    (∑ j : Fin 9, tableGainB s j * X j) =
      ∑ i : Fin 29, tableGainWeight s i * (tableGainE *ᵥ X) i := by
  simp only [tableGainB, Finset.sum_mul, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

theorem tableGain_actual_lower {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hs : 2 ≤ s) (hs6 : s ≤ 6) :
    (∑ j : Fin 9, tableGainB s j * tableFeedbackActualVector δ j) ≤
      wuImprovementLimit false δ s := by
  rw [tableGainB_composition]
  calc
    _ ≤ ∑ i : Fin 29, tableGainWeight s i *
        wuImprovementLimit true δ (tableFeedbackR (i.val + 1)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (tableGain_actual_upper_endpoints hδ hδhi i) (tableGainWeight_nonneg s i))
    _ ≤ _ := tableGain_actual_clipped_lower hδ hδhi hs hs6

theorem tableGain_certified_seed_lower {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hs : 2 ≤ s) (hs6 : s ≤ 6)
    {q : Fin 9 → ℝ} (hq : ∀ j, q j ≤ tableFeedbackActualVector δ j) :
    (∑ j : Fin 9, tableGainB s j * q j) ≤ wuImprovementLimit false δ s := by
  exact (Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left (hq j) (tableGainB_nonneg s j))).trans
    (tableGain_actual_lower hδ hδhi hs hs6)

theorem tableGainB_six (j : Fin 9) : tableGainB 6 j = 0 := by
  simp only [tableGainB, tableGainWeight_six, zero_mul, Finset.sum_const_zero]

end Wu2008DoubleSieve
