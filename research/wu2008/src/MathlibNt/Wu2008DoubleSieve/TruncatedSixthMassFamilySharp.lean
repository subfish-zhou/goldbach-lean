import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassFamily

/-!
# Sharp finite-family count mass with sign-safe effective coefficients

The coarse rectangles and source parameters are fixed before the
threshold. Only rectangles with positive perturbed coefficient are
included in the constructed source packing.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem truncatedSixthMass_family_theta_sharp {δ ε : ℝ}
    (hε : 0 < ε) (K : Finset ℕ) (a b c d w : ℕ → ℝ)
    (hg : ∀ k ∈ K, a k ≤ b k ∧ c k ≤ d k ∧
      truncatedSixthLowerAlpha ≤ a k ∧ truncatedSixthLowerBeta ≤ c k ∧
      truncatedSixthLowerAdmissibleRegion δ (b k) (d k))
    (hw : ∀ k ∈ K, 0 ≤ w k) :
    ∀ᶠ N : ℕ in atTop,
      ((∑ k ∈ K, w k * truncatedSixthMassRectangleCoefficient δ (a k) (b k) (c k) (d k)) - ε) *
        truncatedSixthMassScale N ≤
      ∑ k ∈ K, w k * truncatedSixthMassPackingTheta N δ (a k) (b k) (c k) (d k) := by
  let e := ε / (K.card + 1 : ℝ)
  have he : 0 < e := by dsimp [e]; positivity
  have hpoint (k : ℕ) (hk : k ∈ K) : ∀ᶠ N : ℕ in atTop,
      (w k * truncatedSixthMassRectangleCoefficient δ (a k) (b k) (c k) (d k) - e) *
          truncatedSixthMassScale N ≤
        w k * truncatedSixthMassPackingTheta N δ (a k) (b k) (c k) (d k) := by
    have hw0 := hw k hk
    have hwp : 0 < w k + 1 := by linarith
    have hgeom := hg k hk
    filter_upwards [truncatedSixthMass_packing_theta_sharp hgeom.1 hgeom.2.1 hgeom.2.2.1
      hgeom.2.2.2.1 hgeom.2.2.2.2 (div_pos he hwp), eventually_ge_atTop (4 : ℕ)] with N hmass hN
    have hB : 0 ≤ truncatedSixthMassScale N := by
      unfold truncatedSixthMassScale
      exact div_nonneg (mul_nonneg (wuSingularSeries_pos N (by omega)).le (Nat.cast_nonneg N))
        (sq_nonneg _)
    have hpay : w k * (e / (w k + 1)) ≤ e := by
      rw [← mul_div_assoc, div_le_iff₀ hwp]
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hmass hw0
    have hpaid := mul_le_mul_of_nonneg_right hpay hB
    nlinarith
  filter_upwards [(eventually_all_finset K).mpr hpoint, eventually_ge_atTop (4 : ℕ)] with N hall hN
  have hB : 0 ≤ truncatedSixthMassScale N := by
    unfold truncatedSixthMassScale
    exact div_nonneg (mul_nonneg (wuSingularSeries_pos N (by omega)).le (Nat.cast_nonneg N))
      (sq_nonneg _)
  have hsum := sum_le_sum (fun k hk => hall k hk)
  rw [← sum_mul, sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum
  have hpay : (K.card : ℝ) * e ≤ ε := by
    dsimp [e]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < K.card + 1)]
    nlinarith
  exact (mul_le_mul_of_nonneg_right (by linarith) hB).trans hsum


end Wu2008DoubleSieve
