import MathlibNt.Wu2008DoubleSieve.SecondFunctionalJointTailMass
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact positive rectangle masses for the original selected-coordinate density. -/
namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass
open Set MeasureTheory
open scoped BigOperators
open SecondFunctionalJointTail

noncomputable def coordinateWeight {n : ℕ} (j i : Fin n) (x : ℝ) : ℝ :=
  (1 / x) * (if i = j then 1 / x else 1)

theorem weight_product {n : ℕ} (j : Fin n) (t : Fin n → ℝ) :
    geometricWeight j t = ∏ i, coordinateWeight j i (t i) := by
  unfold coordinateWeight
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq' ]
  simp only [Finset.mem_univ, if_true]
  simp only [geometricWeight, continuousDensity, div_eq_mul_inv, one_mul]

theorem coordinate_integrable {n : ℕ} (j i : Fin n) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (coordinateWeight j i) (Icc a b) := by
  apply ContinuousOn.integrableOn_Icc
  change ContinuousOn (fun x => coordinateWeight j i x) (Icc a b)
  have hc : ContinuousOn (fun x : ℝ => 1 / x) (Icc a b) :=
    continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt (ha.trans_le hx.1))
  by_cases h : i = j
  · simpa [coordinateWeight, h] using! hc.mul hc
  · simpa [coordinateWeight, h] using hc

theorem reciprocal_square_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, (1 / x) * (1 / x)) = 1 / a - 1 / b := by
  have hc : ContinuousOn (fun x : ℝ => (1 / x) * (1 / x)) (Icc a b) := by
    have hi : ContinuousOn (fun x : ℝ => 1 / x) (Icc a b) :=
      continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt (ha.trans_le hx.1))
    exact hi.mul hi
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun y : ℝ => -(1 / y))
      ((1 / x) * (1 / x)) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hn : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
    convert! (hasDerivAt_inv hn).neg using 1
    · funext y
      simp only [Pi.neg_apply, one_div]
    · simp [one_div, pow_two]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc hab)
  simpa only [neg_sub_neg] using he

theorem coordinate_integral {n : ℕ} (j i : Fin n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in Icc a b, coordinateWeight j i x) =
      if i = j then 1 / a - 1 / b else Real.log (b / a) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  by_cases h : i = j
  · simpa [coordinateWeight, h] using reciprocal_square_integral ha hab
  · simpa [coordinateWeight, h] using integral_one_div_of_pos ha (ha.trans_le hab)

/-- Actual absolute integrability, including zero-width rectangles. -/
theorem rectangle_integrable {n : ℕ} (j : Fin n) (A B : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) :
    IntegrableOn (geometricWeight j) (continuousRectangle A B) := by
  change Integrable _ ((Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict _)
  rw [continuousRectangle, Measure.restrict_pi_pi]
  rw [show geometricWeight j = (fun t => ∏ i, coordinateWeight j i (t i)) from
    funext (weight_product j)]
  exact Integrable.fintype_prod (fun i => coordinate_integrable j i (hA i))

/-- Fubini and genuine one-variable primitives for the original weight. -/
theorem rectangle_mass {n : ℕ} (j : Fin n) (A B : Fin n → ℝ)
    (hA : ∀ i, 0 < A i) (hAB : ∀ i, A i ≤ B i) :
    geometricMass j (continuousRectangle A B) =
      ∏ i, if i = j then 1 / A i - 1 / B i else Real.log (B i / A i) := by
  have _hi := rectangle_integrable j A B hA
  change (∫ t, geometricWeight j t
    ∂((Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict _)) = _
  rw [continuousRectangle, Measure.restrict_pi_pi]
  simp_rw [weight_product]
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_congr rfl (fun i _ => coordinate_integral j i (hA i) (hAB i))

end Wu2008DoubleSieve.SecondFunctionalGeometricMass
