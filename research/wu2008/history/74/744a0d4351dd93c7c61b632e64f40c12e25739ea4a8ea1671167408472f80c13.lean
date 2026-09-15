import SrcFifthGainCells

namespace WuSource.SrcFifthGain
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

def staircase (h : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 13, (cell j).indicator (fun _ => h (15+j)) s

def gridGain (h : ℕ → ℝ) : ℝ :=
  8*∑ j ∈ Finset.range 13, cellWeight j*h (15+j)

def directedGain (h w : ℕ → ℝ) : ℝ :=
  8*∑ j ∈ Finset.range 13, w j*h (15+j)

theorem staircase_measurable (h : ℕ → ℝ) : Measurable (staircase h) := by
  unfold staircase cell
  fun_prop (disch := exact measurableSet_Ioc)

theorem staircase_bound (h : ℕ → ℝ) (s : ℝ) :
    |staircase h s| ≤ ∑ j ∈ Finset.range 13, |h (15+j)| := by
  unfold staircase
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : s ∈ cell j
  · simp [indicator_of_mem hj]
  · simp [indicator_of_notMem hj]

theorem staircase_kernel_integrable (h : ℕ → ℝ) :
    Integrable (profileKernel (staircase h)) :=
  profile_kernel_integrable (staircase_measurable h) (fun s _ => staircase_bound h s)

theorem staircase_nonneg {h : ℕ → ℝ}
    (hn : ∀ j < 13, 0 ≤ h (15+j)) (s : ℝ) : 0 ≤ staircase h s := by
  apply Finset.sum_nonneg
  intro j hj
  by_cases hs : s ∈ cell j
  · simpa only [indicator_of_mem hs] using hn j (Finset.mem_range.mp hj)
  · simp [indicator_of_notMem hs]

theorem staircase_on_cell (h : ℕ → ℝ) {j : ℕ} (hj : j < 13) {s : ℝ}
    (hs : s ∈ cell j) : staircase h s = h (15+j) := by
  classical
  unfold staircase
  rw [Finset.sum_eq_single j]
  · exact indicator_of_mem hs _
  · intro k _ hkj
    exact indicator_of_notMem (fun hk => hkj (cell_unique hk hs)) _
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hj))

theorem staircase_off_cells (h : ℕ → ℝ) {s : ℝ}
    (hs : ∀ j < 13, s ∉ cell j) : staircase h s = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  exact indicator_of_notMem (hs j (Finset.mem_range.mp hj)) _

theorem staircase_le_actual {h : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    (hc : ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j)))
    {s : ℝ} (hs : s ∈ Icc s0 FifthClassicalShape.q) :
    staircase h s ≤ wuImprovementLimit false δ s := by
  classical
  by_cases he : ∃ j < 13, s ∈ cell j
  · obtain ⟨j, hj, hsj⟩ := he
    rw [staircase_on_cell h hj hsj]
    have hg := cell_geometry hj
    exact (hc j hj).trans (wuImprovementLimit_lower_antitone hδ (by linarith)
      (parameter_in_core hs) hg.2.2.2.2 (hsj.2.trans hg.2.2.2.1))
  · have hz : ∀ j < 13, s ∉ cell j := by simpa only [not_exists, not_and] using he
    rw [staircase_off_cells h hz]
    have hp := parameter_in_core hs
    exact wuImprovementLimit_nonneg false hδ (by linarith) (by linarith [hp.1]) hp.2

theorem weighted_cell_integrable (h : ℕ → ℝ) {j : ℕ} (hj : j < 13) :
    Integrable ((cell j).indicator (fun s => h (15+j)*weight s)) := by
  have hi : IntegrableOn weight (cell j) := (cell_weight_integrable hj).1
  have hi' : IntegrableOn (fun s => h (15+j)*weight s) (cell j) :=
    hi.const_mul (h (15+j))
  exact hi'.integrable_indicator measurableSet_Ioc

theorem weighted_cell_integral (h : ℕ → ℝ) {j : ℕ} (hj : j < 13) :
    (∫ s, (cell j).indicator (fun s => h (15+j)*weight s) s) =
      cellWeight j*h (15+j) := by
  rw [integral_indicator measurableSet_Ioc, integral_const_mul]
  rw [cell, ← intervalIntegral.integral_of_le (cell_geometry hj).2.1]
  unfold cellWeight
  ring

theorem scalar_staircase_eq_grid (h : ℕ → ℝ) :
    scalarGain (staircase h) = gridGain h := by
  have hf : (fun s => staircase h s*weight s) =
      fun s => ∑ j ∈ Finset.range 13, (cell j).indicator (fun s => h (15+j)*weight s) s := by
    funext s
    unfold staircase
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : s ∈ cell j <;> simp [hj]
  have hs : Function.support (fun s => staircase h s*weight s) ⊆
      Icc s0 FifthClassicalShape.q := by
    intro s hs
    by_contra hn
    apply hs
    have hz : staircase h s = 0 := by
      apply staircase_off_cells
      intro j hj hsj
      have hg := cell_geometry hj
      exact hn ⟨hg.1.trans hsj.1.le, hsj.2.trans hg.2.2.1⟩
    change staircase h s*weight s = 0
    rw [hz, zero_mul]
  unfold scalarGain gridGain
  rw [← truncatedSixthMass_integral_eq_interval FifthClassicalShape.parameters.2.1.le hs,
    hf, integral_finsetSum _ (fun j hj => weighted_cell_integrable h (Finset.mem_range.mp hj))]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact weighted_cell_integral h (Finset.mem_range.mp hj)

theorem source_staircase_eq_grid (h : ℕ → ℝ) :
    sourceGain (staircase h) = gridGain h := by
  rw [source_eq_scalar (staircase_kernel_integrable h), scalar_staircase_eq_grid]

theorem grid_gain_uniform {h : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hc : ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j))) :
    gridGain h ≤ fifthHOnlyIntegral δ := by
  rw [← source_staircase_eq_grid, source_eq_triangle (staircase_kernel_integrable h)]
  exact triangle_gain_uniform (staircase_kernel_integrable h) hδ hd
    (fun s _ => staircase_nonneg hn s) (fun _s hs => staircase_le_actual hδ hd hc hs)

theorem directed_gain_le_grid {h w : ℕ → ℝ}
    (hn : ∀ j < 13, 0 ≤ h (15+j)) (hw : ∀ j < 13, w j ≤ cellWeight j) :
    directedGain h w ≤ gridGain h := by
  unfold directedGain gridGain
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum (fun j hj =>
    mul_le_mul_of_nonneg_right (hw j (Finset.mem_range.mp hj)) (hn j (Finset.mem_range.mp hj)))

theorem grid_count {h : ℕ → ℝ}
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hc : ∀ δ : ℝ, 0 < δ → δ ≤ 1/1000 →
      ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+gridGain h-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) := by
  rw [← source_staircase_eq_grid]
  exact source_profile_count (staircase_kernel_integrable h) (fun s _ => staircase_nonneg hn s)
    (fun δ hδ hd _s hs => staircase_le_actual hδ hd (hc δ hδ hd) hs) hε

theorem directed_threshold_count {h w : ℕ → ℝ} {g : ℝ}
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hc : ∀ δ : ℝ, 0 < δ → δ ≤ 1/1000 →
      ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j)))
    (hw : ∀ j < 13, w j ≤ cellWeight j) (hg : g ≤ directedGain h w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+g-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) := by
  obtain ⟨T, hT, hcN⟩ := grid_count hn hc hε
  have hg' := hg.trans (directed_gain_le_grid hn hw)
  refine ⟨T, hT, fun N hN he => ?_⟩
  have hm := mul_le_mul_of_nonneg_right
    (show fifthPairFlin+g-ε ≤ fifthPairFlin+gridGain h-ε by linarith)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))
  have hm' : (fifthPairFlin+g-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      (fifthPairFlin+gridGain h-ε)*wuSingularSeries N*N/log N^(2 : ℕ) := by
    simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hm
  exact hm'.trans (hcN N hN he)

end
end WuSource.SrcFifthGain
