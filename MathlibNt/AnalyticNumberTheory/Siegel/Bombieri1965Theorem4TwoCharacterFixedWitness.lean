import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterValueUpperBound
import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterWeightedSum

/-!
# Comparison against one fixed genuine real zero

The witness and its actual zero are chosen before the target character.
Induction is to the product of the levels, without a coprimality assumption.
The diagonal is handled by equality of the naturally ordered L-series.
-/

open Complex Finset Filter
open scoped Topology

namespace DirichletCharacter

/-- Equality on the natural numbers identifies actual L-values, even when
the two character levels are different. -/
theorem LFunction_one_eq_of_nat_values_eq {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (heq : ∀ n : ℕ, χ n = ψ n) :
    χ.LFunction 1 = ψ.LFunction 1 := by
  have hχlim := DirichletLConditionalValueSeries.tendsto_sum_range_orderedValueSeries
    χ hχ 1 (by norm_num)
  have hψlim := DirichletLConditionalValueSeries.tendsto_sum_range_orderedValueSeries
    ψ hψ 1 (by norm_num)
  rw [DirichletLConditionalValueSeries.orderedValueSeries_eq_LFunction_of_re_pos] at hχlim hψlim
  simp only [heq] at hχlim
  exact tendsto_nhds_unique hχlim hψlim

end DirichletCharacter

namespace AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4

open DirichletCharacter

/-- Combining the genuine residue lower bound with the subpower upper bound
recovers the target's original L-value, retaining its induction loss. -/
theorem original_value_lower_bound_of_common_level_real_zero
    {q Q : ℕ} [NeZero q] [NeZero Q] (hq : q ∣ Q)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ Q)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχquad : χ ^ 2 = 1) (hψquad : ψ ^ 2 = 1)
    (hne : changeLevel hq χ ≠ ψ) {β a : ℝ}
    (hβ : 7 / 8 ≤ β) (hβ1 : β < 1) (hzero : ψ.LFunction (β : ℂ) = 0)
    (ha : 0 < a) :
    ((1 - β) / (2 * (5000 : ℝ) ^ (8 * (1 - β)) * (3 + 1 / a) ^ 3)) *
        (Q : ℝ) ^ (-(24 * (1 - β) + 3 * a)) ≤ (χ.LFunction 1).re := by
  have hχQ : changeLevel hq χ ≠ 1 :=
    fun h => hχ ((changeLevel_eq_one_iff hq).mp h)
  have hχQquad := sq_changeLevel_eq_one hq hχquad
  have hprod := mul_ne_one_of_quadratic_ne hψquad hne
  have hlower := twoCharacterResidue_re_lower_bound_of_real_zero
    (changeLevel hq χ) ψ hχQ hψ hχQquad hψquad hne hβ hβ1
    (Or.inr (Or.inl hzero))
  have hupper := twoCharacterResidue_re_le_original_value_mul_subpower
    hq χ ψ hχ hχquad hψ hprod ha
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hendpoint :
      ((5000 * (Q : ℝ) ^ 3) ^ 8) ^ (1 - β) =
        (5000 : ℝ) ^ (8 * (1 - β)) * (Q : ℝ) ^ (24 * (1 - β)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    congr 2
    ring
  have hpow :
      (Q : ℝ) ^ (3 * a) * (Q : ℝ) ^ (24 * (1 - β)) =
        (Q : ℝ) ^ (24 * (1 - β) + 3 * a) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  have h := (div_le_iff₀ (by positivity :
      0 < 2 * ((5000 * (Q : ℝ) ^ 3) ^ 8) ^ (1 - β))).mp
    (hlower.trans hupper)
  rw [hendpoint] at h
  have h' :
      1 - β ≤ (χ.LFunction 1).re *
        (2 * (5000 : ℝ) ^ (8 * (1 - β)) * (3 + 1 / a) ^ 3) *
        (Q : ℝ) ^ (24 * (1 - β) + 3 * a) := by
    calc
      _ ≤ _ := h
      _ = _ := by rw [← hpow]; ring
  rw [Real.rpow_neg hQ.le, ← div_eq_mul_inv, div_div]
  apply (div_le_iff₀ (by positivity)).mpr
  simpa only [mul_assoc] using h'

/-- One fixed primitive witness gives a uniform comparison for all distinct
primitive targets; the fixed level is absorbed into the positive constant. -/
theorem exists_fixed_witness_distinct_lower_bound
    {r : ℕ} [NeZero r] (ψ : DirichletCharacter ℂ r)
    (hψprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) (hψquad : ψ ^ 2 = 1)
    {β a : ℝ} (hβ : 7 / 8 ≤ β) (hβ1 : β < 1)
    (hzero : ψ.LFunction (β : ℂ) = 0) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 → (∃ n : ℕ, χ n ≠ ψ n) →
        c * (q : ℝ) ^ (-(24 * (1 - β) + 3 * a)) ≤ (χ.LFunction 1).re := by
  let e : ℝ := 24 * (1 - β) + 3 * a
  let k : ℝ := (1 - β) /
    (2 * (5000 : ℝ) ^ (8 * (1 - β)) * (3 + 1 / a) ^ 3)
  have hk : 0 < k := by dsimp [k]; positivity
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  refine ⟨k * (r : ℝ) ^ (-e), mul_pos hk (Real.rpow_pos_of_pos hr _), ?_⟩
  intro q _ χ hχprim hχ hχquad hne
  let hqQ : q ∣ q * r := dvd_mul_right q r
  let hrQ : r ∣ q * r := dvd_mul_left r q
  have hψQ : changeLevel hrQ ψ ≠ 1 :=
    fun h => hψ ((changeLevel_eq_one_iff hrQ).mp h)
  have hneQ := changeLevel_ne_of_primitive_values hqQ hrQ χ ψ hχprim hψprim hne
  have hzeroQ := (LFunction_changeLevel_real_eq_zero_iff hrQ ψ
    (by linarith : 0 < β) (Or.inl hψ)).mpr hzero
  have h := original_value_lower_bound_of_common_level_real_zero hqQ χ
    (changeLevel hrQ ψ) hχ hψQ hχquad (sq_changeLevel_eq_one hrQ hψquad)
    hneQ hβ hβ1 hzeroQ ha
  change k * ((q * r : ℕ) : ℝ) ^ (-e) ≤ _ at h
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg q) hr.le] at h
  calc
    _ = _ := by ring
    _ ≤ _ := h

/-- The same witness bounds every target. Equality of the natural character
values uses its actual positive L-value, not an enumeration of conductors. -/
theorem exists_fixed_witness_lower_bound
    {r : ℕ} [NeZero r] (ψ : DirichletCharacter ℂ r)
    (hψprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) (hψquad : ψ ^ 2 = 1)
    {β a : ℝ} (hβ : 7 / 8 ≤ β) (hβ1 : β < 1)
    (hzero : ψ.LFunction (β : ℂ) = 0) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
        c * (q : ℝ) ^ (-(24 * (1 - β) + 3 * a)) ≤ (χ.LFunction 1).re := by
  obtain ⟨c, hc, hcomp⟩ := exists_fixed_witness_distinct_lower_bound
    ψ hψprim hψ hψquad hβ hβ1 hzero ha
  have hL := LFunction_apply_one_re_pos_of_sq_eq_one hψquad hψ
  refine ⟨min c (ψ.LFunction 1).re, lt_min hc hL, ?_⟩
  intro q _ χ hχprim hχ hχquad
  by_cases hne : ∃ n : ℕ, χ n ≠ ψ n
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg q) _)).trans
        (hcomp q χ hχprim hχ hχquad hne)
  · have heq : ∀ n : ℕ, χ n = ψ n := by simpa only [not_exists, not_not] using hne
    rw [LFunction_one_eq_of_nat_values_eq χ ψ hχ hψ heq]
    have hp : (q : ℝ) ^ (-(24 * (1 - β) + 3 * a)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      · linarith
    calc
      _ ≤ (ψ.LFunction 1).re * (q : ℝ) ^ (-(24 * (1 - β) + 3 * a)) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
      _ ≤ (ψ.LFunction 1).re := by nlinarith

end AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4
