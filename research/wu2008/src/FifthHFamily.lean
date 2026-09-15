import FifthHMeshCount
import MathlibNt.Wu2008DoubleSieve.FifthPairFamily
namespace Wu2008DoubleSieve

noncomputable def fifthHWeight (δ : ℝ) (n : ℕ) (j : ℕ × ℕ) : ℝ :=
  wuLowerCoefficient (truncatedSixthLowerS δ (truncatedSixthClosureHi n j.1)
    (truncatedSixthClosureHi n j.2)) +
  wuImprovementLimit false δ (truncatedSixthLowerS δ (truncatedSixthClosureHi n j.1)
    (truncatedSixthClosureHi n j.2))
open Finset Real Filter
open scoped Classical Topology

noncomputable def fifthHCellSum (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ fifthPairInner n, fifthHWeight δ n j * truncatedSixthClosureRcoef δ n j

noncomputable def fifthHPerturbedSum (δ η : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ fifthPairInner n,
    max 0 (fifthHWeight δ n j - η) * truncatedSixthClosureRcoef δ n j

noncomputable def fifthHTotalR (δ : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ fifthPairInner n, truncatedSixthClosureRcoef δ n j

theorem fifthH_perturbation {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000)
    (η : ℝ) (n : ℕ) :
    fifthHCellSum δ n - η * fifthHTotalR δ n ≤ fifthHPerturbedSum δ η n := by
  unfold fifthHCellSum fifthHTotalR fifthHPerturbedSum
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_le_sum
  intro j hj
  have h := mul_le_mul_of_nonneg_right
    (le_max_right 0 (fifthHWeight δ n j - η))
    (fifthPair_rcoef_nonneg hδ hδhi hj)
  simpa only [sub_mul] using h

theorem fifthH_family_count {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hη : 0 < η) (hε : 0 < ε)
    (n : ℕ) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (fifthHPerturbedSum δ η n - ε) * truncatedSixthMassScale N ≤ (fifthPairCount N : ℝ) := by
  let C : ℝ := (fifthPairInner n).card
  let e := ε / (C + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hclass := (eventually_all_finset (fifthPairInner n)).mpr
    (fun j hj => fifthH_inner_cell_count hδ hδhi hη he hj)
  filter_upwards [hclass, eventually_ge_atTop (4 : ℕ)] with N hclass hN hEven
  have h1 := sum_le_sum (fun j hj => hclass j hj hEven)
  simp only [← add_sub_assoc] at h1
  change (∑ j ∈ fifthPairInner n, (max 0 (fifthHWeight δ n j - η) *
    truncatedSixthClosureRcoef δ n j - e) * truncatedSixthMassScale N) ≤ _ at h1
  rw [← sum_mul, sum_sub_distrib, sum_const, nsmul_eq_mul] at h1
  have hmain := h1.trans (fifthPair_family_counts_le (by omega))
  have hbudget : C * e ≤ ε := by
    dsimp [e]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < C + 1)]
    nlinarith
  have hpaid := mul_le_mul_of_nonneg_right hbudget (truncatedSixthClosure_scale_nonneg hN)
  change (_ - C * e) * truncatedSixthMassScale N ≤ _ at hmain
  unfold fifthHPerturbedSum
  nlinarith

/-- Every finite inner approximation has its actual coefficient lower bound. -/
theorem fifthH_unperturbed_family_count {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hε : 0 < ε) (n : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthHCellSum δ n - ε) * truncatedSixthMassScale N ≤ (fifthPairCount N : ℝ) := by
  have hR : 0 ≤ fifthHTotalR δ n :=
    sum_nonneg (fun _ hj => fifthPair_rcoef_nonneg hδ.le hδhi hj)
  let η := min 1 (ε / (2 * (fifthHTotalR δ n + 1)))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηcost : η * fifthHTotalR δ n ≤ ε / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (fifthHTotalR δ n + 1))).mp
      (min_le_right 1 (ε / (2 * (fifthHTotalR δ n + 1))))
    change η * (2 * (fifthHTotalR δ n + 1)) ≤ ε at h
    nlinarith
  have hmain := fifthH_family_count hδ hδhi hη (half_pos hε) n
  obtain ⟨T, hT⟩ := eventually_atTop.mp hmain
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN he
  have hN4 := (le_max_left 4 T).trans hN
  apply le_trans (mul_le_mul_of_nonneg_right
    (show fifthHCellSum δ n - ε ≤ fifthHPerturbedSum δ η n - ε / 2 by
      linarith [fifthH_perturbation hδ.le hδhi η n]) (truncatedSixthClosure_scale_nonneg hN4))
  exact hT N ((le_max_right 4 T).trans hN) he

end Wu2008DoubleSieve
