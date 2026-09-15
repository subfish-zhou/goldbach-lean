import MathlibNt.Wu2008DoubleSieve.FifthPairCell
namespace Wu2008DoubleSieve
open Finset Real Filter
open scoped Classical Topology

noncomputable def fifthPairCellSum (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ fifthPairInner n, truncatedSixthClosureWeight false δ n j * truncatedSixthClosureRcoef δ n j

noncomputable def fifthPairPerturbedSum (δ η : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ fifthPairInner n,
    max 0 (truncatedSixthClosureWeight false δ n j - 15 * η) * truncatedSixthClosureRcoef δ n j

noncomputable def fifthPairTotalR (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ fifthPairInner n, truncatedSixthClosureRcoef δ n j

theorem fifthPair_rcoef_nonneg {δ : ℝ} {n : ℕ} {j : ℕ × ℕ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000) (hj : j ∈ fifthPairInner n) :
    0 ≤ truncatedSixthClosureRcoef δ n j := by
  have hg := fifthPair_inner_geometry hj
  have hα := truncatedSixthLower_parameters.1
  have ha := hα.trans_le hg.1
  have hab := (truncatedSixthClosure_lo_lt_hi n j.1).le
  have hcd := (truncatedSixthClosure_lo_lt_hi n j.2).le
  have hc := ha.trans_le (hab.trans hg.2.1)
  have hden : 0 < truncatedSixthLowerC δ - truncatedSixthClosureLo n j.1 -
      truncatedSixthClosureLo n j.2 := by linarith [fifthPair_inner_level hδ hδhi hj]
  have hlog1 := log_nonneg ((one_le_div ha).mpr hab)
  have hlog2 := log_nonneg ((one_le_div hc).mpr hcd)
  unfold truncatedSixthClosureRcoef truncatedSixthMassRectangleCoefficient
  positivity

theorem fifthPair_perturbation {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000)
    (η : ℝ) (n : ℕ) :
    fifthPairCellSum δ n - 15 * η * fifthPairTotalR δ n ≤ fifthPairPerturbedSum δ η n := by
  unfold fifthPairCellSum fifthPairTotalR fifthPairPerturbedSum
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_le_sum
  intro j hj
  have h := mul_le_mul_of_nonneg_right
    (le_max_right 0 (truncatedSixthClosureWeight false δ n j - 15 * η))
    (fifthPair_rcoef_nonneg hδ hδhi hj)
  simpa only [sub_mul] using h

/-- Disjointness is on actual finite prime pairs, not almost-everywhere geometry. -/
theorem fifthPair_family_counts_le {N n : ℕ} (hN : 1 < N) :
    (∑ j ∈ fifthPairInner n, truncatedSixthClosureCount N
      (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
      (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)) ≤
    (fifthPairCount N : ℝ) := by
  let P := fun j : ℕ × ℕ => truncatedSixthClosurePairs N
    (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
    (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)
  have hsub : (fifthPairInner n).biUnion P ⊆ fifthPairLabels N := by
    intro p hp
    obtain ⟨j, hj, hp⟩ := mem_biUnion.mp hp
    have hg := fifthPair_inner_geometry hj
    exact fifthPair_cell_subset hN hg.1 hg.2.1 hg.2.2 hp
  have hdisj : Set.PairwiseDisjoint (fifthPairInner n : Set (ℕ × ℕ)) P := by
    intro j _ k _ hjk
    exact truncatedSixthClosure_grid_pairs_disjoint hN hjk
  rw [fifthPair_count_eq]
  calc
    _ = ∑ p ∈ (fifthPairInner n).biUnion P,
        (sieveCount N (p.1 * p.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) :=
      (sum_biUnion hdisj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by
      exact_mod_cast (show (0 : ℤ) ≤ sieveCount N _ N _ from Int.natCast_nonneg _))

theorem fifthPair_family_count {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε)
    (n : ℕ) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (fifthPairPerturbedSum δ η n - ε) * truncatedSixthMassScale N ≤ (fifthPairCount N : ℝ) := by
  let C : ℝ := (fifthPairInner n).card
  let e := ε / (C + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hclass := (eventually_all_finset (fifthPairInner n)).mpr
    (fun j hj => fifthPair_cell_count hδ hδhi hη hηhi he hj)
  filter_upwards [hclass, eventually_ge_atTop (4 : ℕ)] with N hclass hN hEven
  have h1 := sum_le_sum (fun j hj => hclass j hj hEven)
  rw [← sum_mul, sum_sub_distrib, sum_const, nsmul_eq_mul] at h1
  have hmain := h1.trans (fifthPair_family_counts_le (by omega))
  have hbudget : C * e ≤ ε := by
    dsimp [e]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < C + 1)]
    nlinarith
  have hpaid := mul_le_mul_of_nonneg_right hbudget (truncatedSixthClosure_scale_nonneg hN)
  change (_ - C * e) * truncatedSixthMassScale N ≤ _ at hmain
  unfold fifthPairPerturbedSum
  nlinarith

/-- Every finite inner approximation has its actual coefficient lower bound. -/
theorem fifthPair_unperturbed_family_count {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hε : 0 < ε) (n : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairCellSum δ n - ε) * truncatedSixthMassScale N ≤ (fifthPairCount N : ℝ) := by
  have hR : 0 ≤ fifthPairTotalR δ n :=
    sum_nonneg (fun _ hj => fifthPair_rcoef_nonneg hδ.le hδhi hj)
  let η := min 1 (ε / (30 * (fifthPairTotalR δ n + 1)))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηhi : η ≤ 1 := min_le_left _ _
  have hηcost : 15 * η * fifthPairTotalR δ n ≤ ε / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 30 * (fifthPairTotalR δ n + 1))).mp
      (min_le_right 1 (ε / (30 * (fifthPairTotalR δ n + 1))))
    change η * (30 * (fifthPairTotalR δ n + 1)) ≤ ε at h
    nlinarith
  have hmain := fifthPair_family_count hδ hδhi hη hηhi (half_pos hε) n
  obtain ⟨T, hT⟩ := eventually_atTop.mp hmain
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN he
  have hN4 := (le_max_left 4 T).trans hN
  apply le_trans (mul_le_mul_of_nonneg_right
    (show fifthPairCellSum δ n - ε ≤ fifthPairPerturbedSum δ η n - ε / 2 by
      linarith [fifthPair_perturbation hδ.le hδhi η n]) (truncatedSixthClosure_scale_nonneg hN4))
  exact hT N ((le_max_right 4 T).trans hN) he

end Wu2008DoubleSieve
