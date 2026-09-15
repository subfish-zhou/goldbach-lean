import MathlibNt.Wu2008DoubleSieve.TruncatedSixthClosureCount

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

noncomputable def truncatedSixthClosurePerturbedSum (gain : Bool) (δ η : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ truncatedSixthClosureInner gain δ n,
    max 0 (truncatedSixthClosureWeight gain δ n j - 15 * η) * truncatedSixthClosureRcoef δ n j

noncomputable def truncatedSixthClosureTotalR (gain : Bool) (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ truncatedSixthClosureInner gain δ n, truncatedSixthClosureRcoef δ n j

theorem truncatedSixthClosure_totalR_nonneg (gain : Bool) (δ : ℝ) (n : ℕ) :
    0 ≤ truncatedSixthClosureTotalR gain δ n :=
  sum_nonneg (fun _ hj => truncatedSixthClosure_rcoef_nonneg hj)

theorem truncatedSixthClosure_perturbation (gain : Bool) (δ η : ℝ) (n : ℕ) :
    truncatedSixthClosureSum gain δ n - 15 * η * truncatedSixthClosureTotalR gain δ n ≤
      truncatedSixthClosurePerturbedSum gain δ η n := by
  unfold truncatedSixthClosureSum truncatedSixthClosureTotalR truncatedSixthClosurePerturbedSum
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_le_sum
  intro j hj
  have h := mul_le_mul_of_nonneg_right
    (le_max_right 0 (truncatedSixthClosureWeight gain δ n j - 15 * η))
    (truncatedSixthClosure_rcoef_nonneg hj)
  simpa only [sub_mul] using h

theorem truncatedSixthClosure_inner_disjoint (δ : ℝ) (n : ℕ) :
    Disjoint (truncatedSixthClosureInner false δ n) (truncatedSixthClosureInner true δ n) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  have hl : truncatedSixthLowerC δ / 2 < truncatedSixthClosureLo n j.2 :=
    (mem_filter.mp hj).2.1.2
  have hu : truncatedSixthClosureHi n j.2 ≤ truncatedSixthLowerC δ / 2 :=
    (mem_filter.mp hk).2.2.2
  linarith [truncatedSixthClosure_lo_lt_hi n j.2]

theorem truncatedSixthClosure_grid_pairs_disjoint {N n : ℕ} (hN : 1 < N) :
    Pairwise (fun j k : ℕ × ℕ =>
      Disjoint
        (truncatedSixthClosurePairs N (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
          (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2))
        (truncatedSixthClosurePairs N (truncatedSixthClosureLo n k.1) (truncatedSixthClosureHi n k.1)
          (truncatedSixthClosureLo n k.2) (truncatedSixthClosureHi n k.2))) := by
  intro j k hjk
  have hsep {i l : ℕ} (h : i < l) : truncatedSixthClosureHi n i ≤ truncatedSixthClosureLo n l := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (show i + 1 ≤ l by omega)
  apply truncatedSixthMass_rectangle_disjoint hN
  rcases lt_trichotomy j.1 k.1 with h | h | h
  · exact Or.inl (hsep h)
  · have hne : j.2 ≠ k.2 := fun h2 => hjk (Prod.ext h h2)
    rcases lt_or_gt_of_ne hne with h2 | h2
    · exact Or.inr (Or.inr (Or.inl (hsep h2)))
    · exact Or.inr (Or.inr (Or.inr (hsep h2)))
  · exact Or.inr (Or.inl (hsep h))

theorem truncatedSixthClosure_counts_le_actual {N n : ℕ} {δ : ℝ}
    (hN : 1 < N) (hδ : 0 < δ) :
    (∑ j ∈ truncatedSixthClosureInner false δ n,
      truncatedSixthClosureCount N
        (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
        (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)) +
    (∑ j ∈ truncatedSixthClosureInner true δ n,
      truncatedSixthClosureCount N
        (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
        (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)) ≤
    (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
      ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
      ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  let K := truncatedSixthClosureInner false δ n ∪ truncatedSixthClosureInner true δ n
  let P := fun j : ℕ × ℕ => truncatedSixthClosurePairs N
    (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
    (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)
  have hsub : K.biUnion P ⊆ truncatedSixthLowerPairs N δ := by
    intro p hp
    obtain ⟨j, hj, hp⟩ := mem_biUnion.mp hp
    rcases mem_union.mp hj with hj | hj
    all_goals
      have hg := truncatedSixthClosure_inner_geometry hj
      exact truncatedSixthClosure_pairs_subset hN hg.1 hg.2.1 hg.2.2 hp
  have hdisj : Set.PairwiseDisjoint (K : Set (ℕ × ℕ)) P := by
    intro j _ k _ hjk
    exact truncatedSixthClosure_grid_pairs_disjoint hN hjk
  have hact := truncatedSixthLower_mask_mass_le hN hδ _ hsub
  rw [sum_biUnion hdisj, show K = _ from rfl, sum_union (truncatedSixthClosure_inner_disjoint δ n)] at hact
  exact hact

theorem truncatedSixthClosure_family_count {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε)
    (n : ℕ) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (truncatedSixthClosurePerturbedSum false δ η n +
        truncatedSixthClosurePerturbedSum true δ η n - ε) * truncatedSixthMassScale N ≤
      (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
        ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
        ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  let C : ℝ := (truncatedSixthClosureInner false δ n).card + (truncatedSixthClosureInner true δ n).card
  let e := ε / (C + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hclass := (eventually_all_finset (truncatedSixthClosureInner false δ n)).mpr
    (fun j hj => truncatedSixthClosure_classical_count hδ hδhi hη hηhi he hj)
  have hgain := (eventually_all_finset (truncatedSixthClosureInner true δ n)).mpr
    (fun j hj => truncatedSixthClosure_gain_count hδ hδhi hη he hj)
  filter_upwards [hclass, hgain, eventually_ge_atTop (4 : ℕ)] with N hclass hgain hN hEven
  have h1 := sum_le_sum (fun j hj => hclass j hj hEven)
  have h2 := sum_le_sum (fun j hj => hgain j hj hEven)
  rw [← sum_mul, sum_sub_distrib, sum_const, nsmul_eq_mul] at h1 h2
  have hmain := (add_le_add h1 h2).trans (truncatedSixthClosure_counts_le_actual (by omega) hδ)
  have hbudget : C * e ≤ ε := by
    dsimp [e]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < C + 1)]
    nlinarith
  have hpaid := mul_le_mul_of_nonneg_right hbudget (truncatedSixthClosure_scale_nonneg hN)
  change (_ - _ * e) * truncatedSixthMassScale N + (_ - _ * e) * truncatedSixthMassScale N ≤ _ at hmain
  dsimp [C] at hpaid
  unfold truncatedSixthClosurePerturbedSum
  nlinarith

end Wu2008DoubleSieve
