import WR2OmegaFourPartition
import WR2OmegaHighPaid

/-! The four published classical window masses fit the fixed-delta high integral. -/
noncomputable section
namespace WuPaper.R2OmegaFour
open Wu2008DoubleSieve WuSource.SrcSingle R2OmegaHigh Real Set MeasureTheory
open scoped Interval BigOperators

private theorem window_bounds (j : Fin 4) :
    (1/4 : ℝ) ≤ psiLeft (index j) ∧ psiLeft (index j) ≤ psiRight (index j) ∧
      psiRight (index j) ≤ 1/3 := by
  fin_cases j <;> norm_num [index, psiLeft, psiRight, psiNode, sourceNode, truncatedSixthLowerAlpha]

private theorem reciprocal_integrable (j : Fin 4) {δ : ℝ} (hh : δ ≤ 1/100) :
    IntervalIntegrable (fun t : ℝ => 1/(t*(1/2-δ-t))) volume
      (psiLeft (index j)) (psiRight (index j)) := by
  have hb := window_bounds j
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hb.2.1]
  apply continuousOn_const.div (by fun_prop)
  intro t ht
  have ht0 : 0 < t := by linarith [hb.1, ht.1]
  have hz : 0 < 1/2-δ-t := by linarith [ht.2, hb.2.2]
  exact (mul_pos ht0 hz).ne'

theorem outer_zero_le (j : Fin 4) {δ : ℝ} (hd : 0 ≤ δ) (hh : δ ≤ 1/100) :
    outerIntegral j 0 ≤ outerIntegral j δ := by
  apply intervalIntegral.integral_mono_on (window_bounds j).2.1
    (reciprocal_integrable j (by norm_num : (0:ℝ) ≤ 1/100)) (reciprocal_integrable j hh)
  intro t ht
  have hb := window_bounds j
  have ht0 : 0 < t := by linarith [hb.1, ht.1]
  have hz : 0 < 1/2-δ-t := by linarith [ht.2, hb.2.2]
  exact div_le_div_of_nonneg_left (by norm_num) (mul_pos ht0 hz)
    (mul_le_mul_of_nonneg_left (by linarith : 1/2-δ-t ≤ 1/2-0-t) ht0.le)

theorem outer_eq_weighted (j : Fin 4) {δ : ℝ} (hd : 0 ≤ δ) (hh : δ ≤ 1/100) :
    outerIntegral j δ =
      ∫ t in psiLeft (index j)..psiRight (index j), SingleUpperQuadrature.weight δ t/t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (window_bounds j).2.1] at ht
  dsimp only
  rw [prime_weight_eq_single j hd hh ht]
  simp only [HighSix.primeWeight, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem edge_bounds {i : ℕ} (hi : 3 ≤ i) (h7 : i ≤ 7) :
    (1/15 : ℝ) ≤ sevenBoundary i ∧ sevenBoundary i ≤ 1/3 := by
  interval_cases i <;> norm_num [sevenBoundary, sourceNode, truncatedSixthLowerAlpha]

theorem outer_sum_eq_middle {δ : ℝ} (hd : 0 ≤ δ) (hh : δ ≤ 1/100) :
    (∑ j : Fin 4, outerIntegral j δ) =
      ∫ t in sevenBoundary 7..sevenBoundary 3, SingleUpperQuadrature.weight δ t/t := by
  have hall := SingleUpperLowEndpoint.density_integrable hd hh
    (le_refl (1/15 : ℝ)) (by norm_num : (1/15 : ℝ) ≤ 1/3) (le_refl (1/3 : ℝ))
  have hi (i j : ℕ) (hi3 : 3 ≤ i) (hi7 : i ≤ 7) (hj3 : 3 ≤ j) (hj7 : j ≤ 7) :
      IntervalIntegrable (fun t => SingleUpperQuadrature.weight δ t/t) volume
        (sevenBoundary i) (sevenBoundary j) := by
    apply hall.mono_set
    rw [uIcc_of_le (by norm_num : (1/15 : ℝ) ≤ 1/3)]
    intro t ht
    have ha := edge_bounds hi3 hi7
    have hb := edge_bounds hj3 hj7
    rcases mem_uIcc.mp ht with ht | ht <;> constructor <;> linarith [ht.1, ht.2]
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hi 7 6 (by omega) (by omega) (by omega) (by omega))
    (hi 6 5 (by omega) (by omega) (by omega) (by omega))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hi 7 5 (by omega) (by omega) (by omega) (by omega))
    (hi 5 4 (by omega) (by omega) (by omega) (by omega))
  have h3 := intervalIntegral.integral_add_adjacent_intervals
    (hi 7 4 (by omega) (by omega) (by omega) (by omega))
    (hi 4 3 (by omega) (by omega) (by omega) (by omega))
  simp_rw [outer_eq_weighted _ hd hh]
  norm_num only [Fin.sum_univ_succ, index, psiLeft, psiRight, psiNode,
    Fin.val_natAdd, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
    if_false, add_zero]
  norm_num only [sevenBoundary, if_false] at h1 h2 h3 ⊢
  linarith only [h1, h2, h3]

theorem four_classical_le_middle {δ : ℝ} (hd : 0 ≤ δ) (hh : δ ≤ 1/100) :
    fourClassical ≤
      4*∫ t in sevenBoundary 7..sevenBoundary 3, SingleUpperQuadrature.weight δ t/t := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => outer_zero_le j hd hh)
  simp_rw [outer_integral_zero] at h
  rw [← outer_sum_eq_middle hd hh]
  unfold fourClassical
  rw [← Finset.mul_sum] at h
  linarith only [h]

end WuPaper.R2OmegaFour
#print axioms WuPaper.R2OmegaFour.four_classical_le_middle
