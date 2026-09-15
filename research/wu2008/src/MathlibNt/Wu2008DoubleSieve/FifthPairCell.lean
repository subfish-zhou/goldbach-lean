import MathlibNt.Wu2008DoubleSieve.FifthPairTheta
namespace Wu2008DoubleSieve
open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def fifthPairInner (n : ℕ) : Finset (ℕ × ℕ) :=
  (truncatedSixthClosureCells n).filter (fun j =>
    truncatedSixthLowerAlpha ≤ truncatedSixthClosureLo n j.1 ∧
    truncatedSixthClosureHi n j.1 ≤ truncatedSixthClosureLo n j.2 ∧
    truncatedSixthClosureHi n j.2 ≤ truncatedSixthLowerBeta)

theorem fifthPair_inner_geometry {n : ℕ} {j : ℕ × ℕ} (hj : j ∈ fifthPairInner n) :
    truncatedSixthLowerAlpha ≤ truncatedSixthClosureLo n j.1 ∧
    truncatedSixthClosureHi n j.1 ≤ truncatedSixthClosureLo n j.2 ∧
    truncatedSixthClosureHi n j.2 ≤ truncatedSixthLowerBeta := (mem_filter.mp hj).2

theorem fifthPair_inner_level {δ : ℝ} {n : ℕ} {j : ℕ × ℕ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000) (hj : j ∈ fifthPairInner n) :
    truncatedSixthClosureHi n j.1 + truncatedSixthClosureHi n j.2 <
      truncatedSixthLowerC δ := by
  have hg := fifthPair_inner_geometry hj
  have h1 := (truncatedSixthClosure_lo_lt_hi n j.1).le
  have h2 := (truncatedSixthClosure_lo_lt_hi n j.2).le
  have hb := fifthPair_triangle_bounds hδ hδhi (hg.1.trans h1)
    (hg.2.1.trans h2) hg.2.2
  linarith [hb.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2]

theorem fifthPair_theta_nonneg {N : ℕ} {δ : ℝ} {p : ℕ × ℕ}
    (hN : 4 ≤ N) (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000)
    (hp : p ∈ fifthPairLabels N) :
    0 ≤ truncatedSixthLowerClassicalTheta N δ p := by
  have hs := fifthPair_prime_s_bounds (by omega) hδ hδhi hp
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

theorem fifthPair_cell_weight_le {N n : ℕ} {δ : ℝ} {j p : ℕ × ℕ}
    (hN : 1 < N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000)
    (hj : j ∈ fifthPairInner n)
    (hp : p ∈ truncatedSixthClosurePairs N
      (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
      (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)) :
    truncatedSixthClosureWeight false δ n j ≤ wuLowerCoefficient (truncatedSixthLowerPrimeS N δ p) := by
  have hg := fifthPair_inner_geometry hj
  have hsub := fifthPair_cell_subset hN hg.1 hg.2.1 hg.2.2 hp
  have hs := fifthPair_prime_s_bounds hN hδ.le hδhi hsub
  have hx := truncatedSixthLower_coordinate_window hN (mem_product.mp hp).1
  have hy := truncatedSixthLower_coordinate_window hN (mem_product.mp hp).2
  have hslow := truncatedSixthClosure_s_order (δ := δ) (show
      (log (p.1 : ℝ) / log N, log (p.2 : ℝ) / log N) ≤ truncatedSixthClosureUpper n j from
      ⟨hx.2.le, hy.2.le⟩)
  have hshi := truncatedSixthClosure_s_order (δ := δ) (show truncatedSixthClosureLower n j ≤
      (log (p.1 : ℝ) / log N, log (p.2 : ℝ) / log N) from ⟨hx.1, hy.1⟩)
  rw [← fifthPair_prime_s_eq hN hsub] at hslow hshi
  have h := truncatedSixthClosure_inf_le
    (fun t => (truncatedSixthClosure_coefficient_bounds hδ (by linarith) false t).1) ⟨hslow, hshi⟩
  change truncatedSixthClosureWeight false δ n j ≤
    truncatedSixthClosureCoefficient false δ (truncatedSixthLowerPrimeS N δ p) at h
  simpa only [truncatedSixthClosureCoefficient, Bool.false_eq_true, if_false,
    truncatedSixthMass_clip_eq hs] using h

theorem fifthPair_cell_count {δ η ε : ℝ} {n : ℕ} {j : ℕ × ℕ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε)
    (hj : j ∈ fifthPairInner n) :
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
    have hg := fifthPair_inner_geometry hj
    obtain ⟨T, hT, hclass⟩ :=
      fifthPair_normalized_masked_relative hδ hδhi hη hηhi (half_pos hε)
    filter_upwards [eventually_ge_atTop T,
      fifthPair_cell_theta_sharp
        (truncatedSixthClosure_lo_lt_hi n j.1).le (truncatedSixthClosure_lo_lt_hi n j.2).le
        (truncatedSixthLower_parameters.1.trans_le hg.1)
        (truncatedSixthLower_parameters.1.trans_le
          (hg.1.trans ((truncatedSixthClosure_lo_lt_hi _ _).le.trans hg.2.1)))
        (fifthPair_inner_level hδ.le hδhi hj)
        (show 0 < ε / (2 * L) by positivity)] with N hN hmass he
    have hN4 := hT.trans hN
    let S := truncatedSixthClosurePairs N
      (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
      (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)
    have hS : S ⊆ fifthPairLabels N :=
      fifthPair_cell_subset (by omega) hg.1 hg.2.1 hg.2.2
    have hmain : L * (∑ p ∈ S, truncatedSixthLowerClassicalTheta N δ p) ≤
        truncatedSixthLowerNormalizedMain N δ η S := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (sub_le_sub_right (fifthPair_cell_weight_le (by omega) hδ hδhi hj hp) _)
        (fifthPair_theta_nonneg hN4 hδ.le hδhi (hS hp))
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

end Wu2008DoubleSieve
