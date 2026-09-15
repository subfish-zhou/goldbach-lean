import LowComplementGeometry

namespace LowComplement
open Finset Real Wu2008DoubleSieve MixedSixth Filter
open scoped Classical Topology
noncomputable section

theorem classical_term_nonneg {N : ℕ} {δ : ℝ} {p : ℕ × ℕ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/100)
    (hp : p ∈ truncatedSixthLowerPairs N δ) :
    0 ≤ wuLowerCoefficient (truncatedSixthLowerPrimeS N δ p) * truncatedSixthLowerClassicalTheta N δ p := by
  have hs := truncatedSixthLower_prime_s_bounds (by omega) hδ.le hp
  have ha := (truncatedSixthClosure_coefficient_bounds hδ hδhi false
    (truncatedSixthLowerPrimeS N δ p)).1
  have ha' : 0 ≤ wuLowerCoefficient (truncatedSixthLowerPrimeS N δ p) := by
    simpa only [truncatedSixthClosureCoefficient,Bool.false_eq_true,if_false,
      truncatedSixthMass_clip_eq hs] using ha
  exact mul_nonneg ha' (truncatedSixthClosure_classical_theta_nonneg hN hδ.le hp)

theorem wedge_subset_rest {N n : ℕ} {δ : ℝ} (hN : 1 < N) (hδ : 0 ≤ δ) :
    truncatedSixthLowerWedgePairs N δ ⊆ rest N n δ := by
  intro p hp
  refine mem_sdiff.mpr ⟨(mem_filter.mp hp).1,?_⟩
  intro hl
  obtain ⟨k,hk,hpk⟩ := mem_biUnion.mp hl
  have hg := (actual_geometry hN hδ n).1 k hk
  exact disjoint_left.mp (truncatedSixthLower_box_disjoint_wedge hN hg) hp hpk

def coarsePairs (N n : ℕ) (j : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  truncatedSixthClosurePairs N (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
    (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)

theorem coarse_wedge_subset {N n : ℕ} {δ : ℝ} {j : ℕ × ℕ}
    (hN : 1 < N) (hj : j ∈ truncatedSixthClosureInner false δ n) :
    coarsePairs N n j ⊆ truncatedSixthLowerWedgePairs N δ := by
  intro p hp
  have hg := truncatedSixthClosure_inner_geometry hj
  have hl : truncatedSixthLowerC δ/2 < truncatedSixthClosureLo n j.2 := (mem_filter.mp hj).2.1.2
  have hq := (mem_primeWindow.mp (mem_product.mp hp).2).2.2.1
  refine mem_filter.mpr ⟨truncatedSixthClosure_pairs_subset hN hg.1 hg.2.1 hg.2.2 hp,?_⟩
  exact (rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hN) hl).trans_le hq

theorem classical_grid_le_rest {N n : ℕ} {δ : ℝ} (hN : 4 ≤ N)
    (hδ : 0 < δ) (hδhi : δ < 1/100) :
    (∑ j ∈ truncatedSixthClosureInner false δ n,
      truncatedSixthClosureWeight false δ n j *
        ∑ p ∈ coarsePairs N n j, truncatedSixthLowerClassicalTheta N δ p) ≤
      truncatedSixthLowerNormalizedMain N δ 0 (rest N n δ) := by
  have hN1 : 1 < N := by omega
  have hsub : (truncatedSixthClosureInner false δ n).biUnion (coarsePairs N n) ⊆ rest N n δ := by
    intro p hp
    obtain ⟨j,hj,hp⟩ := mem_biUnion.mp hp
    exact wedge_subset_rest hN1 hδ.le (coarse_wedge_subset hN1 hj hp)
  have hd : Set.PairwiseDisjoint (truncatedSixthClosureInner false δ n : Set (ℕ × ℕ))
      (coarsePairs N n) := by
    intro i _ j _ hij
    exact truncatedSixthClosure_grid_pairs_disjoint hN1 hij
  have h1 : (∑ j ∈ truncatedSixthClosureInner false δ n,
      truncatedSixthClosureWeight false δ n j *
        ∑ p ∈ coarsePairs N n j, truncatedSixthLowerClassicalTheta N δ p) ≤
      ∑ j ∈ truncatedSixthClosureInner false δ n,
        ∑ p ∈ coarsePairs N n j,
          wuLowerCoefficient (truncatedSixthLowerPrimeS N δ p)*truncatedSixthLowerClassicalTheta N δ p := by
    apply sum_le_sum
    intro j hj
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hg := truncatedSixthClosure_inner_geometry hj
    exact mul_le_mul_of_nonneg_right (truncatedSixthClosure_classical_weight_le hN1 hδ hδhi hj hp)
      (truncatedSixthClosure_classical_theta_nonneg hN hδ.le
        (truncatedSixthClosure_pairs_subset hN1 hg.1 hg.2.1 hg.2.2 hp))
  rw [← sum_biUnion hd] at h1
  apply h1.trans
  simp only [truncatedSixthLowerNormalizedMain,mul_zero,sub_zero]
  apply sum_le_sum_of_subset_of_nonneg hsub
  intro p hp _
  exact classical_term_nonneg hN hδ hδhi (mem_sdiff.mp hp).1

end
end LowComplement
