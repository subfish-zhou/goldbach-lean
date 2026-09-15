import MathlibNt.Wu2008DoubleSieve.Gamma5MassQuadrature

/-!
# Bilateral two-prime arithmetic mass

The finite comparison is valid on arbitrary pair masks. The uniform
quadrature conclusion is for every source rectangle, with the old product
arbitrary and all shared factors retained.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

noncomputable def gamma5MassArithmeticPairs (N d : ℕ) (R A B C D : ℝ) : ℝ :=
  ∑ x ∈ gamma5MassPrimePairs N R A B C D,
    gamma5MassAtom d x.1 * gamma5MassAtom (d * x.1) x.2 *
      gamma5MassH (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2)

/-- Bilateral comparison on every finite pair mask, including shared factors. -/
theorem gamma5Mass_mask_bilateral (d : ℕ) (R Z : ℝ) (X : Finset (ℕ × ℕ))
    (hZ : 4 ≤ Z) (hX : ∀ x ∈ X, Z ≤ (x.1 : ℝ) ∧ Z ≤ (x.2 : ℝ)) :
    (∑ x ∈ X, gamma5MassH (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2) /
        ((x.1 : ℝ) * x.2)) ≤
      ∑ x ∈ X, gamma5MassAtom d x.1 * gamma5MassAtom (d * x.1) x.2 *
        gamma5MassH (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2) ∧
    (∑ x ∈ X, gamma5MassAtom d x.1 * gamma5MassAtom (d * x.1) x.2 *
        gamma5MassH (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2)) ≤
      (1 + 4 / Z) ^ 2 *
        ∑ x ∈ X, gamma5MassH (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2) /
          ((x.1 : ℝ) * x.2) := by
  constructor
  · apply sum_le_sum
    intro x hx
    have h := mul_le_mul_of_nonneg_right
      (gamma5Mass_atoms_bilateral (d := d) hZ (hX x hx).1 (hX x hx).2).1
      (gamma5Mass_H_bounds _ _).1.le
    convert h using 1
    ring
  · rw [mul_sum]
    apply sum_le_sum
    intro x hx
    have h := mul_le_mul_of_nonneg_right
      (gamma5Mass_atoms_bilateral (d := d) hZ (hX x hx).1 (hX x hx).2).2
      (gamma5Mass_H_bounds _ _).1.le
    exact h.trans_eq (by ring)

theorem gamma5Mass_pairs_bilateral {N : ℕ} (d : ℕ) {R A B C D α : ℝ}
    (hR : 1 < R) (hA : gamma5MassA ≤ A) (hC : gamma5MassA ≤ C)
    (hZ : (N : ℝ) ^ α ≤ R ^ gamma5MassA) (hfour : 4 ≤ (N : ℝ) ^ α) :
    gamma5MassReciprocalPairs N R A B C D ≤ gamma5MassArithmeticPairs N d R A B C D ∧
      gamma5MassArithmeticPairs N d R A B C D ≤
        (1 + 4 / (N : ℝ) ^ α) ^ 2 * gamma5MassReciprocalPairs N R A B C D := by
  apply gamma5Mass_mask_bilateral d R ((N : ℝ) ^ α) _ hfour
  intro x hx
  obtain ⟨hp, hq⟩ := mem_product.mp (mem_filter.mp hx).1
  exact ⟨(gamma5Mass_prime_lower hR hA hZ x.1 hp).2,
    (gamma5Mass_prime_lower hR hC hZ x.2 hq).2⟩

theorem gamma5Mass_arithmetic_pair_uniform {α β ε : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≤ β * gamma5MassA) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ R : ℝ, (N : ℝ) ^ β ≤ R → ∀ d : ℕ,
      ∀ A B C D : ℝ,
      gamma5MassA ≤ A → A ≤ B → B ≤ gamma5ClassicalB →
      gamma5MassA ≤ C → C ≤ D → D ≤ gamma5ClassicalB →
      |gamma5MassArithmeticPairs N d R A B C D - gamma5MassRectangleIntegral A B C D| < ε := by
  let τ := min 1 (ε / 4)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : τ ≤ ε / 4 := min_le_right _ _
  have hdecay : Tendsto (fun N : ℕ => (1 + 4 / (N : ℝ) ^ α) ^ (2 : ℕ) - 1)
      atTop (𝓝 0) := by
    have h := tendsto_const_nhds.div_atTop
      ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop) (a := (4 : ℝ))
    convert ((tendsto_const_nhds.add h).pow 2).sub_const 1 using 1 <;> norm_num
  filter_upwards [gamma5Mass_pair_quadrature_uniform hα hβ hαβ hτ,
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)),
    hdecay.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 130 by positivity)),
    eventually_ge_atTop (2 : ℕ)] with N hquad hfour hsmall hN
  intro R hNR d A B C D hA hAB hB hC hCD hD
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hR : 1 < R := (one_lt_rpow hN1 hβ).trans_le hNR
  have hZ : (N : ℝ) ^ α ≤ R ^ gamma5MassA := by
    calc
      _ ≤ (N : ℝ) ^ (β * gamma5MassA) := rpow_le_rpow_of_exponent_le hN1.le hαβ
      _ = ((N : ℝ) ^ β) ^ gamma5MassA := rpow_mul (Nat.cast_nonneg _) _ _
      _ ≤ _ := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg _) _) hNR
        (by norm_num [gamma5MassA, gamma5ClassicalS])
  have hb := gamma5Mass_pairs_bilateral d hR hA hC hZ hfour
  have hq := hquad R hNR A B C D hA hAB hB hC hCD hD
  have hi := gamma5Mass_rectangle_bounds hA hAB hB hC hCD hD
  have hq' := abs_lt.mp hq
  have hU : gamma5MassReciprocalPairs N R A B C D ≤ 65 := by linarith
  have hF : 0 ≤ (1 + 4 / (N : ℝ) ^ α) ^ (2 : ℕ) - 1 := by
    have h : 0 ≤ 4 / (N : ℝ) ^ α := by positivity
    nlinarith
  have hcost := mul_le_mul_of_nonneg_left hU hF
  rw [abs_lt]
  constructor <;> nlinarith

end Wu2008DoubleSieve
