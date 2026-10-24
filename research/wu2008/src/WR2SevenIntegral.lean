import WR2SevenPublicationCount
import WR2OmegaFourIntegral

/-! The seven published classical window masses fit the fixed-delta high integral. -/
noncomputable section
namespace WuPaper.R2Seven
open Wu2008DoubleSieve WuSource.SrcSingle R2OmegaHigh Real Set MeasureTheory
open scoped Interval BigOperators

def windowIntegral (j : Fin 7) (δ : ℝ) : ℝ :=
  ∫ t in psiLeft j..psiRight j, 1/(t*(1/2-δ-t))

private theorem prime_weight_eq_single (j : Fin 7) {δ t : ℝ}
    (hd : 0 ≤ δ) (hh : δ ≤ 1/100) (ht : t ∈ Icc (psiLeft j) (psiRight j)) :
    SingleUpperQuadrature.weight δ t = HighSix.primeWeight δ t := by
  revert ht
  refine Fin.addCases (m := 3) (n := 4) (fun i => ?_) (fun i => ?_) j
  · exact R2GammaHigh.prime_weight_eq_single i hd hh
  · exact R2OmegaHigh.prime_weight_eq_single i hd hh

private theorem window_integral_zero (j : Fin 7) :
    windowIntegral j 0 = 2*psiLogWeight j := by
  refine Fin.addCases (m := 3) (n := 4) (fun i => ?_) (fun i => ?_) j
  · have h := R2GammaHigh.prime_integral_zero i
    change 4*windowIntegral (i.castAdd 4) 0 = _ at h
    linarith only [h]
  · exact R2OmegaHigh.outer_integral_zero i

private theorem window_bounds (j : Fin 7) :
    (1/4 : ℝ) ≤ psiLeft j ∧ psiLeft j ≤ psiRight j ∧
      psiRight j ≤ 1/3 := by
  fin_cases j <;> norm_num [psiLeft, psiRight, psiNode, sourceNode, truncatedSixthLowerAlpha]

private theorem reciprocal_integrable (j : Fin 7) {δ : ℝ} (hh : δ ≤ 1/100) :
    IntervalIntegrable (fun t : ℝ => 1/(t*(1/2-δ-t))) volume
      (psiLeft j) (psiRight j) := by
  have hb := window_bounds j
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hb.2.1]
  apply continuousOn_const.div (by fun_prop)
  intro t ht
  have ht0 : 0 < t := by linarith [hb.1, ht.1]
  have hz : 0 < 1/2-δ-t := by linarith [ht.2, hb.2.2]
  exact (mul_pos ht0 hz).ne'

theorem outer_zero_le (j : Fin 7) {δ : ℝ} (hd : 0 ≤ δ) (hh : δ ≤ 1/100) :
    windowIntegral j 0 ≤ windowIntegral j δ := by
  apply intervalIntegral.integral_mono_on (window_bounds j).2.1
    (reciprocal_integrable j (by norm_num : (0:ℝ) ≤ 1/100)) (reciprocal_integrable j hh)
  intro t ht
  have hb := window_bounds j
  have ht0 : 0 < t := by linarith [hb.1, ht.1]
  have hz : 0 < 1/2-δ-t := by linarith [ht.2, hb.2.2]
  exact div_le_div_of_nonneg_left (by norm_num) (mul_pos ht0 hz)
    (mul_le_mul_of_nonneg_left (by linarith : 1/2-δ-t ≤ 1/2-0-t) ht0.le)

theorem outer_eq_weighted (j : Fin 7) {δ : ℝ} (hd : 0 ≤ δ) (hh : δ ≤ 1/100) :
    windowIntegral j δ =
      ∫ t in psiLeft j..psiRight j, SingleUpperQuadrature.weight δ t/t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (window_bounds j).2.1] at ht
  dsimp only
  rw [prime_weight_eq_single j hd hh ht]
  simp only [HighSix.primeWeight, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem edge_bounds {i : ℕ} (hi : i ≤ 7) :
    (1/15 : ℝ) ≤ sevenBoundary i ∧ sevenBoundary i ≤ 1/3 := by
  interval_cases i <;> norm_num [sevenBoundary, sourceNode, truncatedSixthLowerAlpha]

theorem window_sum_eq_middle {δ : ℝ} (hd : 0 ≤ δ) (hh : δ ≤ 1/100) :
    (∑ j : Fin 7, windowIntegral j δ) =
      ∫ t in sevenBoundary 7..(1/3 : ℝ), SingleUpperQuadrature.weight δ t/t := by
  have hall := SingleUpperLowEndpoint.density_integrable hd hh
    (le_refl (1/15 : ℝ)) (by norm_num : (1/15 : ℝ) ≤ 1/3) (le_refl (1/3 : ℝ))
  have hi (i j : ℕ) (hi7 : i ≤ 7) (hj7 : j ≤ 7) :
      IntervalIntegrable (fun t => SingleUpperQuadrature.weight δ t/t) volume
        (sevenBoundary i) (sevenBoundary j) := by
    apply hall.mono_set
    rw [uIcc_of_le (by norm_num : (1/15 : ℝ) ≤ 1/3)]
    intro t ht
    have ha := edge_bounds hi7
    have hb := edge_bounds hj7
    rcases mem_uIcc.mp ht with ht | ht <;> constructor <;> linarith [ht.1, ht.2]
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hi 7 6 (by omega) (by omega)) (hi 6 5 (by omega) (by omega))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hi 7 5 (by omega) (by omega)) (hi 5 4 (by omega) (by omega))
  have h3 := intervalIntegral.integral_add_adjacent_intervals
    (hi 7 4 (by omega) (by omega)) (hi 4 3 (by omega) (by omega))
  have h4 := intervalIntegral.integral_add_adjacent_intervals
    (hi 7 3 (by omega) (by omega)) (hi 3 2 (by omega) (by omega))
  have h5 := intervalIntegral.integral_add_adjacent_intervals
    (hi 7 2 (by omega) (by omega)) (hi 2 1 (by omega) (by omega))
  have h6 := intervalIntegral.integral_add_adjacent_intervals
    (hi 7 1 (by omega) (by omega)) (hi 1 0 (by omega) (by omega))
  simp_rw [outer_eq_weighted _ hd hh]
  norm_num only [Fin.sum_univ_succ, psiLeft, psiRight, psiNode,
    Fin.val_zero, Fin.val_succ, Nat.reduceAdd, if_false, if_true, add_zero]
  norm_num only [sevenBoundary, if_false, if_true] at h1 h2 h3 h4 h5 h6 ⊢
  linarith only [h1,h2,h3,h4,h5,h6]

theorem seven_classical_le_middle {δ : ℝ} (hd : 0 ≤ δ) (hh : δ ≤ 1/100) :
    sevenClassical ≤
      4*∫ t in sevenBoundary 7..(1/3 : ℝ), SingleUpperQuadrature.weight δ t/t := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => outer_zero_le j hd hh)
  simp_rw [window_integral_zero] at h
  rw [← window_sum_eq_middle hd hh]
  unfold sevenClassical
  rw [← Finset.mul_sum] at h
  linarith only [h]

end WuPaper.R2Seven
#print axioms WuPaper.R2Seven.seven_classical_le_middle
