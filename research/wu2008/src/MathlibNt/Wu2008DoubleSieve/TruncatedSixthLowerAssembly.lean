import MathlibNt.Wu2008DoubleSieve.TruncatedSixthLowerRelative

/-!
# Disjoint classical-wedge and genuine admissible-box count assembly

Only the wedge receives the classical summand in this assembly.
The admissible boxes receive a + h once. Packing hypotheses are finite
geometry, not analytic estimates. No assertion that a packing exhausts
the polygon integral is made here.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

noncomputable def truncatedSixthLowerWedgePairs (N : ℕ) (δ : ℝ) : Finset (ℕ × ℕ) :=
  (truncatedSixthLowerPairs N δ).filter
    (fun t => (N : ℝ) ^ (truncatedSixthLowerC δ / 2) < t.2)

noncomputable def truncatedSixthLowerBoxPairs (N : ℕ) (Δ x y : ℝ) : Finset (ℕ × ℕ) :=
  primeWindow N ((N : ℝ) ^ x / Δ) ((N : ℝ) ^ x) ×ˢ
    primeWindow N ((N : ℝ) ^ y / Δ) ((N : ℝ) ^ y)

theorem truncatedSixthLower_box_pairs_subset {N : ℕ} {δ Δ x y : ℝ}
    (hN : 1 < N) (hxy : truncatedSixthLowerAdmissibleRegion δ x y)
    (hplo : (N : ℝ) ^ truncatedSixthLowerAlpha ≤ (N : ℝ) ^ x / Δ)
    (hqlo : (N : ℝ) ^ truncatedSixthLowerBeta ≤ (N : ℝ) ^ y / Δ) :
    truncatedSixthLowerBoxPairs N Δ x y ⊆ truncatedSixthLowerPairs N δ := by
  intro b hb
  obtain ⟨hp, hq⟩ := mem_product.mp hb
  have hp' := mem_primeWindow.mp hp
  have hq' := mem_primeWindow.mp hq
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hN0 : (0 : ℝ) < N := by linarith
  apply mem_filter.mpr
  constructor
  · apply mem_product.mpr
    constructor
    · exact mem_primeWindow.mpr ⟨hp'.1, hp'.2.1, hplo.trans hp'.2.2.1,
        hp'.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hNR hxy.1.2.1)⟩
    · exact mem_primeWindow.mpr ⟨hq'.1, hq'.2.1, hqlo.trans hq'.2.2.1,
        hq'.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hNR hxy.1.2.2.2.1)⟩
  · calc
      (b.1 : ℝ) * b.2 ≤ (N : ℝ) ^ x * (N : ℝ) ^ y :=
        mul_le_mul hp'.2.2.2.le hq'.2.2.2.le (Nat.cast_nonneg _) (rpow_nonneg hN0.le _)
      _ = (N : ℝ) ^ (x + y) := (rpow_add hN0 x y).symm
      _ ≤ _ := rpow_le_rpow_of_exponent_le hNR hxy.1.2.2.2.2

theorem truncatedSixthLower_box_disjoint_wedge {N : ℕ} {δ Δ x y : ℝ}
    (hN : 1 < N) (hxy : truncatedSixthLowerAdmissibleRegion δ x y) :
    Disjoint (truncatedSixthLowerWedgePairs N δ)
      (truncatedSixthLowerBoxPairs N Δ x y) := by
  apply disjoint_left.mpr
  intro b hw hb
  have hw' := (mem_filter.mp hw).2
  have hb' := (mem_primeWindow.mp (mem_product.mp hb).2).2.2.2
  have hpow := rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hN.le : (1 : ℝ) ≤ N) hxy.2
  exact (not_lt_of_ge (hb'.trans_le hpow).le) hw'

theorem truncatedSixthLower_finite_packing_actual {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε)
    (G : Finset ℝ) (hG : ∀ t ∈ G, 2 ≤ t ∧ t ≤ 5) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ,
      1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
      Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
      ∀ (I : Finset ℕ) (x y t : ℕ → ℝ),
      (∀ j ∈ I, truncatedSixthLowerAdmissibleRegion δ (x j) (y j)) →
      (∀ j ∈ I, (N : ℝ) ^ truncatedSixthLowerAlpha ≤ (N : ℝ) ^ (x j) / Δ) →
      (∀ j ∈ I, (N : ℝ) ^ truncatedSixthLowerBeta ≤ (N : ℝ) ^ (y j) / Δ) →
      (∀ j ∈ I, t j ∈ G ∧ t j ≤ truncatedSixthLowerS δ (x j) (y j)) →
      (Set.PairwiseDisjoint (I : Set ℕ)
        (fun j => truncatedSixthLowerBoxPairs N Δ (x j) (y j))) →
      truncatedSixthLowerNormalizedMain N δ η (truncatedSixthLowerWedgePairs N δ) +
        (∑ j ∈ I, (wuLowerCoefficient (t j) + wuImprovementLimit false δ (t j) - η) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
            (convolutionWuWindows N Δ ![(N : ℝ) ^ (y j), (N : ℝ) ^ (x j)])) -
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
          ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
          ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨T1, hT1, hclassical⟩ :=
    truncatedSixthLower_normalized_masked_relative hδ hη hηhi hε
  obtain ⟨T2, _, hgain⟩ := truncatedSixthLower_finite_grid_gain hδ hδhi hη G hG
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he Δ hΔlo hΔhi I x y t hxy hplo hqlo ht hdisj
  have hN4 : 4 ≤ N := hT1.trans ((le_max_left _ _).trans hN)
  have hN1 : 1 < N := by omega
  let B := fun j => truncatedSixthLowerBoxPairs N Δ (x j) (y j)
  let W := truncatedSixthLowerWedgePairs N δ
  let F := fun b : ℕ × ℕ =>
    (sieveCount N (b.1 * b.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ)
  have hW : W ⊆ truncatedSixthLowerPairs N δ := filter_subset _ _
  have hw := hclassical N ((le_max_left _ _).trans hN) he W hW
  have hb : ∀ j ∈ I,
      (wuLowerCoefficient (t j) + wuImprovementLimit false δ (t j) - η) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
          (convolutionWuWindows N Δ ![(N : ℝ) ^ (y j), (N : ℝ) ^ (x j)]) ≤
        ∑ b ∈ B j, F b := by
    intro j hj
    have hqlo' : (N : ℝ) ^ truncatedSixthLowerAlpha ≤ (N : ℝ) ^ (y j) / Δ :=
      (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1.le)
        truncatedSixthLower_parameters.2.1.le).trans (hqlo j hj)
    have h := hgain N ((le_max_right _ _).trans hN) he Δ (x j) (y j)
      hΔlo hΔhi (hxy j hj) (hplo j hj) hqlo' (t j) (ht j hj).1 (ht j hj).2
    convert h using 1
    dsimp [B, F, truncatedSixthLowerBoxPairs]
    rw [sum_product, sum_product, sum_comm]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    rw [mul_comm p q]
  have hU : W ∪ I.biUnion B ⊆ truncatedSixthLowerPairs N δ := by
    apply union_subset hW
    intro b hb
    obtain ⟨j, hj, hb⟩ := mem_biUnion.mp hb
    exact truncatedSixthLower_box_pairs_subset hN1 (hxy j hj) (hplo j hj) (hqlo j hj) hb
  have hWU : Disjoint W (I.biUnion B) := by
    apply disjoint_left.mpr
    intro b hw hb
    obtain ⟨j, hj, hb⟩ := mem_biUnion.mp hb
    exact disjoint_left.mp (truncatedSixthLower_box_disjoint_wedge hN1 (hxy j hj)) hw hb
  have htotal := truncatedSixthLower_mask_mass_le hN1 hδ _ hU
  change (∑ b ∈ W ∪ I.biUnion B, F b) ≤ _ at htotal
  rw [sum_union hWU, sum_biUnion hdisj] at htotal
  have hsum := sum_le_sum hb
  change _ ≤ ∑ b ∈ W, F b at hw
  linarith

end Wu2008DoubleSieve
