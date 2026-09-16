import Wu18938Campaign.M1.Confirmed.FullFirstKernel

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FullProfile

open Wu2008DoubleSieve Real Set MeasureTheory NodeExtension ActualNineFeedback FiniteProfile
open WuPaper.R2Matrix
open scoped Classical Interval BigOperators

theorem sampled_profile_le {H : ℝ → ℝ} (hH : Antitone H)
    (hH0 : ∀ v ∈ Icc (1 : ℝ) 3, 0 ≤ H v) {z : Fin 9 → ℝ}
    (hz : ∀ j, z j ≤ H (upperNode j)) {v : ℝ} (hv : v ∈ Icc (1 : ℝ) 3) :
    nineProfile z v ≤ H v := by
  by_cases hh : ∃ j : Fin 9, v ∈ Ioc (upperLeft j) (upperNode j)
  · obtain ⟨j,hj⟩ := hh
    rw [nineProfile_cell _ hj]
    exact (hz j).trans (hH hj.2)
  · have he : nineProfile z v = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact indicator_of_notMem (fun hj => hh ⟨j,hj⟩) _
    rw [he]
    exact hH0 v hv

theorem source_matrix_le_row {H : ℝ → ℝ} (hH : Antitone H)
    (hH0 : ∀ v ∈ Icc (1 : ℝ) 3, 0 ≤ H v) (hHb : ∀ v, |H v| ≤ 1)
    {z : Fin 9 → ℝ} (hz : ∀ j, z j ≤ H (upperNode j))
    (j : Fin 9) (δ : ℝ) (hδ : δ < 1 / 2) :
    sourceForcing δ j + (∑ k : Fin 9, sourceMatrix j k * z k) ≤ rowGain δ H j := by
  rw [row_gain_original_kernel hH hHb j δ hδ,← sourceFeedback_expansion,
    sourceFeedback_eq_original_integral]
  apply add_le_add le_rfl
  apply intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 3)
    (sourceKernel_weighted_integrable j (nineProfile_integrable z))
    (sourceKernel_weighted_integrable j hH.intervalIntegrable)
  intro v hv
  exact mul_le_mul_of_nonneg_right (sampled_profile_le hH hH0 hz hv)
    (sourceKernel_nonnegative j hv)

theorem staircase_depth_mono (z : Fin 9 → ℝ) (v : ℝ) :
    Monotone (fun n => staircase z n v) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

theorem clipped_row_le_staircase (z : Fin 9 → ℝ) (j : Fin 9) :
    clippedHeight (z j) ≤ staircase z 9 (upperNode j) := by
  have hh : clippedHeight (z j) ≤ staircase z (j.val + 1) (upperNode j) := by
    simp only [staircase, dif_pos j.isLt]
    simpa only [stepProfile,if_pos le_rfl] using
      (le_max_right (staircase z j.val (upperNode j))
        (stepProfile z j (upperNode j)))
  exact hh.trans (staircase_depth_mono z _ (by omega : j.val + 1 ≤ 9))

def sourceIteration (δ : ℝ) : ℕ → Fin 9 → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun j => max (sourceIteration δ n j)
      (clippedHeight (sourceForcing δ j +
        ∑ k : Fin 9, sourceMatrix j k * sourceIteration δ n k))

theorem source_iteration_bounds (δ : ℝ) (n : ℕ) (j : Fin 9) :
    0 ≤ sourceIteration δ n j ∧ sourceIteration δ n j ≤ 1 / 16 := by
  induction n with
  | zero => norm_num [sourceIteration]
  | succ n ih =>
    exact ⟨ih.1.trans (le_max_left _ _),max_le ih.2 (clippedHeight_bounds _).2⟩

theorem source_iteration_le_profile (δ : ℝ) (hδ : δ < 1 / 2) (n : ℕ) (j : Fin 9) :
    sourceIteration δ n j ≤ untruncatedProfile δ n (upperNode j) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have hm := source_matrix_le_row (profile_antitone δ n)
      (fun v _ => (profile_bounds δ n v).1) (profile_abs_bound δ n) ih j δ hδ
    have hc : clippedHeight (sourceForcing δ j +
        ∑ k : Fin 9, sourceMatrix j k * sourceIteration δ n k) ≤
        clippedHeight (rowGain δ (untruncatedProfile δ n) j) :=
      max_le_max le_rfl (min_le_min le_rfl hm)
    exact max_le_max (ih j) (hc.trans (clipped_row_le_staircase _ j))

theorem source_iteration_actual {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (n : ℕ) (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ j : Fin 9,
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (upperNode j) ≤
        (1 - sourceIteration δ n j + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := profile_actual hδ hδhi n m η ε hη he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb j
  have hh := hT N hN heven i Δ V hb (upperNode j)
    (upperNode_bounds j).1 (upperNode_bounds j).2
  exact hh.trans (mul_le_mul_of_nonneg_right
    (by linarith only [source_iteration_le_profile δ (by linarith) n j])
    (Rebox.theta_nonneg hb (by omega) hη hδ))

end Wu18938Campaign.M1.Confirmed.FullProfile
