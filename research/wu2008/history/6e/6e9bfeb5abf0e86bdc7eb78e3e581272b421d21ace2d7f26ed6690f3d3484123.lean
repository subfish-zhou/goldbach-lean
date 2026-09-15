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

theorem truncatedSixthMass_family_sharp_actual {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε)
    (K : Finset ℕ) (a b c d s : ℕ → ℝ)
    (hg : ∀ k ∈ K, a k ≤ b k ∧ c k ≤ d k ∧
      truncatedSixthLowerAlpha ≤ a k ∧ truncatedSixthLowerBeta ≤ c k ∧
      truncatedSixthLowerAdmissibleRegion δ (b k) (d k))
    (hs : ∀ k ∈ K, 2 ≤ s k ∧ s k ≤ 5 ∧ s k ≤ truncatedSixthLowerS δ (b k) (d k))
    (hsep : ∀ k ∈ K, ∀ l ∈ K, k ≠ l →
      b k ≤ a l ∨ b l ≤ a k ∨ d k ≤ c l ∨ d l ≤ c k) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthLowerNormalizedMain N δ η (truncatedSixthLowerWedgePairs N δ) +
        ((∑ k ∈ K, max 0 (wuLowerCoefficient (s k) + wuImprovementLimit false δ (s k) - η) *
          truncatedSixthMassRectangleCoefficient δ (a k) (b k) (c k) (d k)) - ε) *
            truncatedSixthMassScale N ≤
        (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
          ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
          ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  let w := fun k => wuLowerCoefficient (s k) + wuImprovementLimit false δ (s k) - η
  let J := K.filter (fun k => 0 < w k)
  have hsub : J ⊆ K := filter_subset _ _
  obtain ⟨T1, hT1, hcount⟩ := truncatedSixthMass_family_actual hδ hδhi hη hηhi
    (half_pos hε) J a b c d s
    (fun k hk => hg k (hsub hk)) (fun k hk => hs k (hsub hk))
    (fun k hk l hl => hsep k (hsub hk) l (hsub hl))
  obtain ⟨T2, hmass⟩ := eventually_atTop.mp (truncatedSixthMass_family_theta_sharp
    (half_pos hε) J a b c d w (fun k hk => hg k (hsub hk))
    (fun _ hk => (mem_filter.mp hk).2.le))
  have hsum :
      (∑ k ∈ J, w k * truncatedSixthMassRectangleCoefficient δ (a k) (b k) (c k) (d k)) =
      ∑ k ∈ K, max 0 (w k) * truncatedSixthMassRectangleCoefficient δ (a k) (b k) (c k) (d k) := by
    dsimp only [J]
    rw [sum_filter]
    apply sum_congr rfl
    intro k _
    by_cases hk : 0 < w k
    · simp [hk, max_eq_right hk.le]
    · simp [hk, max_eq_left (le_of_not_gt hk)]
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hact := hcount N ((le_max_left _ _).trans hN) he
  have hm := hmass N ((le_max_right _ _).trans hN)
  rw [hsum] at hm
  change _ + (∑ k ∈ J, w k * truncatedSixthMassPackingTheta N δ (a k) (b k) (c k) (d k)) -
    ε / 2 * truncatedSixthMassScale N ≤ _ at hact
  change _ + ((∑ k ∈ K, max 0 (w k) *
    truncatedSixthMassRectangleCoefficient δ (a k) (b k) (c k) (d k)) - ε) *
    truncatedSixthMassScale N ≤ _
  nlinarith

end Wu2008DoubleSieve
