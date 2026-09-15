import MathlibNt.Wu2008DoubleSieve.TruncatedSixthClosureClassical

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem truncatedSixthClosure_scale_nonneg {N : ℕ} (hN : 4 ≤ N) :
    0 ≤ truncatedSixthMassScale N := by
  have hC := wuSingularSeries_pos N (by omega)
  unfold truncatedSixthMassScale
  positivity

theorem truncatedSixthClosure_classical_theta_nonneg {N : ℕ} {δ : ℝ} {p : ℕ × ℕ}
    (hN : 4 ≤ N) (hδ : 0 ≤ δ) (hp : p ∈ truncatedSixthLowerPairs N δ) :
    0 ≤ truncatedSixthLowerClassicalTheta N δ p := by
  have hs := truncatedSixthLower_prime_s_bounds (by omega) hδ hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log ((N : ℝ) ^ truncatedSixthLowerAlpha) := by
    rw [log_rpow hN0]
    exact mul_pos truncatedSixthLower_parameters.1
      (log_pos (by exact_mod_cast (show 1 < N by omega)))
  have hl : 0 ≤ log ((N : ℝ) ^ truncatedSixthLowerC δ / (p.1 * p.2 : ℕ)) := by
    have h := (le_div_iff₀ hlog).mp hs.1
    linarith
  have hC := wuSingularSeries_pos N (by omega)
  have hli : 0 ≤ logarithmicIntegral N :=
    (show (0 : ℝ) ≤ N / (2 * log N) by positivity).trans (box_trueLi_lower hN)
  unfold truncatedSixthLowerClassicalTheta
  positivity

theorem truncatedSixthClosure_classical_weight_le {N n : ℕ} {δ : ℝ} {j p : ℕ × ℕ}
    (hN : 1 < N) (hδ : 0 < δ) (hδhi : δ < 1 / 100)
    (hj : j ∈ truncatedSixthClosureInner false δ n)
    (hp : p ∈ truncatedSixthClosurePairs N
      (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
      (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)) :
    truncatedSixthClosureWeight false δ n j ≤ wuLowerCoefficient (truncatedSixthLowerPrimeS N δ p) := by
  have hg := truncatedSixthClosure_inner_geometry hj
  have hsub := truncatedSixthClosure_pairs_subset hN hg.1 hg.2.1 hg.2.2 hp
  have hs := truncatedSixthLower_prime_s_bounds hN hδ.le hsub
  have hx := truncatedSixthLower_coordinate_window hN (mem_product.mp hp).1
  have hy := truncatedSixthLower_coordinate_window hN (mem_product.mp hp).2
  have hslow := truncatedSixthClosure_s_order (δ := δ) (show
      (log (p.1 : ℝ) / log N, log (p.2 : ℝ) / log N) ≤ truncatedSixthClosureUpper n j from
      ⟨hx.2.le, hy.2.le⟩)
  have hshi := truncatedSixthClosure_s_order (δ := δ) (show truncatedSixthClosureLower n j ≤
      (log (p.1 : ℝ) / log N, log (p.2 : ℝ) / log N) from ⟨hx.1, hy.1⟩)
  rw [← truncatedSixthLower_prime_s_eq hN hsub] at hslow hshi
  have h := truncatedSixthClosure_inf_le
    (fun t => (truncatedSixthClosure_coefficient_bounds hδ hδhi false t).1) ⟨hslow, hshi⟩
  change truncatedSixthClosureWeight false δ n j ≤
    truncatedSixthClosureCoefficient false δ (truncatedSixthLowerPrimeS N δ p) at h
  simpa only [truncatedSixthClosureCoefficient, Bool.false_eq_true, if_false,
    truncatedSixthMass_clip_eq hs] using h

theorem truncatedSixthClosure_classical_count {δ η ε : ℝ} {n : ℕ} {j : ℕ × ℕ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε)
    (hj : j ∈ truncatedSixthClosureInner false δ n) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (max 0 (truncatedSixthClosureWeight false δ n j - 15 * η) *
        truncatedSixthClosureRcoef δ n j - ε) * truncatedSixthMassScale N ≤
      truncatedSixthClosureCount N
        (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
        (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2) := by
  let L := truncatedSixthClosureWeight false δ n j - 15 * η
  by_cases hL : L ≤ 0
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN _
    rw [max_eq_left hL, zero_mul, zero_sub]
    exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le)
      (truncatedSixthClosure_scale_nonneg hN)).trans (truncatedSixthClosure_count_nonneg _ _ _ _ _)
  · have hL0 : 0 < L := lt_of_not_ge hL
    have hg := truncatedSixthClosure_inner_geometry hj
    obtain ⟨T, hT, hclass⟩ :=
      truncatedSixthLower_normalized_masked_relative hδ hη hηhi (half_pos hε)
    filter_upwards [eventually_ge_atTop T,
      truncatedSixthClosure_classical_theta_sharp
        (truncatedSixthClosure_lo_lt_hi n j.1).le (truncatedSixthClosure_lo_lt_hi n j.2).le
        hg.1 hg.2.1 hg.2.2 (show 0 < ε / (2 * L) by positivity)] with N hN hmass he
    have hN4 := hT.trans hN
    let S := truncatedSixthClosurePairs N
      (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
      (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)
    have hS : S ⊆ truncatedSixthLowerPairs N δ :=
      truncatedSixthClosure_pairs_subset (by omega) hg.1 hg.2.1 hg.2.2
    have hmain : L * (∑ p ∈ S, truncatedSixthLowerClassicalTheta N δ p) ≤
        truncatedSixthLowerNormalizedMain N δ η S := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (sub_le_sub_right (truncatedSixthClosure_classical_weight_le (by omega) hδ hδhi hj hp) _)
        (truncatedSixthClosure_classical_theta_nonneg hN4 hδ.le (hS hp))
    have hact := hclass N hN he S hS
    have hm := mul_le_mul_of_nonneg_left hmass hL0.le
    have heq : L * ((truncatedSixthClosureRcoef δ n j - ε / (2 * L)) * truncatedSixthMassScale N) =
        (L * truncatedSixthClosureRcoef δ n j - ε / 2) * truncatedSixthMassScale N := by field_simp
    change L * ((truncatedSixthClosureRcoef δ n j - ε / (2 * L)) * truncatedSixthMassScale N) ≤ _ at hm
    rw [heq] at hm
    have hact' : truncatedSixthLowerNormalizedMain N δ η S -
        ε / 2 * truncatedSixthMassScale N ≤ truncatedSixthClosureCount N
        (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
        (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2) := by
      simpa only [truncatedSixthMassScale, truncatedSixthClosureCount, S, mul_div_assoc, mul_assoc] using hact
    rw [max_eq_right hL0.le]
    change (L * truncatedSixthClosureRcoef δ n j - ε) * truncatedSixthMassScale N ≤ _
    linarith

theorem truncatedSixthClosure_gain_count {δ η ε : ℝ} {n : ℕ} {j : ℕ × ℕ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hη : 0 < η) (hε : 0 < ε)
    (hj : j ∈ truncatedSixthClosureInner true δ n) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (max 0 (truncatedSixthClosureWeight true δ n j - 15 * η) *
        truncatedSixthClosureRcoef δ n j - ε) * truncatedSixthMassScale N ≤
      truncatedSixthClosureCount N
        (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
        (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2) := by
  let L := truncatedSixthClosureWeight true δ n j - 15 * η
  by_cases hL : L ≤ 0
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN _
    rw [max_eq_left hL, zero_mul, zero_sub]
    exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le)
      (truncatedSixthClosure_scale_nonneg hN)).trans (truncatedSixthClosure_count_nonneg _ _ _ _ _)
  · have hL0 : 0 < L := lt_of_not_ge hL
    have hg := truncatedSixthClosure_inner_geometry hj
    have hbd : truncatedSixthLowerAdmissibleRegion δ
        (truncatedSixthClosureHi n j.1) (truncatedSixthClosureHi n j.2) :=
      (mem_filter.mp hj).2.2
    let s := truncatedSixthLowerS δ (truncatedSixthClosureHi n j.1) (truncatedSixthClosureHi n j.2)
    have hs := (truncatedSixthLower_region_bounds hδ.le hbd.1).2.2.2
    change 2 ≤ s ∧ s ≤ 5 at hs
    let E := wuLowerCoefficient s + wuImprovementLimit false δ s
    have hwE : truncatedSixthClosureWeight true δ n j ≤ E := by
      have h := truncatedSixthClosure_inf_le
        (fun t => (truncatedSixthClosure_coefficient_bounds hδ hδhi true t).1)
        ⟨le_rfl, truncatedSixthClosure_s_order (δ := δ) (truncatedSixthClosure_corners_order n j)⟩
      change truncatedSixthClosureWeight true δ n j ≤ truncatedSixthClosureCoefficient true δ s at h
      change truncatedSixthClosureWeight true δ n j ≤
        wuLowerCoefficient s + wuImprovementLimit false δ s
      simpa only [truncatedSixthClosureCoefficient, if_true, truncatedSixthMassEffective,
        truncatedSixthMass_clip_eq hs] using h
    have htol : 0 < E - L := by dsimp [L]; linarith
    obtain ⟨T, hT, hgain⟩ := truncatedSixthMass_packing_gain_count hδ hδhi htol
      (truncatedSixthClosure_lo_lt_hi n j.1).le (truncatedSixthClosure_lo_lt_hi n j.2).le
      hg.1 hg.2.1 hbd hs.1 hs.2 le_rfl
    filter_upwards [eventually_ge_atTop T,
      truncatedSixthMass_packing_theta_sharp
        (truncatedSixthClosure_lo_lt_hi n j.1).le (truncatedSixthClosure_lo_lt_hi n j.2).le
        hg.1 hg.2.1 hbd (show 0 < ε / L by positivity)] with N hN hmass he
    have hN1 : 1 < N := by omega
    have hact := hgain N hN he
    have hEL : wuLowerCoefficient s + wuImprovementLimit false δ s - (E - L) = L := by
      dsimp [E]
      ring
    rw [hEL] at hact
    let J := truncatedSixthMassPacking N
      (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
      (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)
    let B := truncatedSixthMassPackingBox N (truncatedSixthClosureLo n j.1) (truncatedSixthClosureLo n j.2)
    have hdisj : Set.PairwiseDisjoint (J : Set (ℕ × ℕ)) B := by
      intro i _ k _ hik
      exact truncatedSixthMass_packing_disjoint hN1 _ _ hik
    have hsub : J.biUnion B ⊆ truncatedSixthClosurePairs N
        (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
        (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2) := by
      intro p hp
      obtain ⟨k, hk, hp⟩ := mem_biUnion.mp hp
      exact truncatedSixthMass_packing_box_subset hN1
        (truncatedSixthClosure_lo_lt_hi n j.1).le (truncatedSixthClosure_lo_lt_hi n j.2).le hk hp
    have hsum : (∑ k ∈ J, ∑ p ∈ B k,
        (sieveCount N (p.1 * p.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ)) ≤
        truncatedSixthClosureCount N
          (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
          (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2) := by
      rw [← sum_biUnion hdisj]
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro p _ _
      exact_mod_cast (show (0 : ℤ) ≤ sieveCount N _ N _ from Int.natCast_nonneg _)
    have hm := mul_le_mul_of_nonneg_left hmass hL0.le
    have heq : L * ((truncatedSixthClosureRcoef δ n j - ε / L) * truncatedSixthMassScale N) =
        (L * truncatedSixthClosureRcoef δ n j - ε) * truncatedSixthMassScale N := by field_simp
    change L * ((truncatedSixthClosureRcoef δ n j - ε / L) * truncatedSixthMassScale N) ≤ _ at hm
    rw [heq] at hm
    rw [max_eq_right hL0.le]
    exact hm.trans (hact.trans hsum)

end Wu2008DoubleSieve
