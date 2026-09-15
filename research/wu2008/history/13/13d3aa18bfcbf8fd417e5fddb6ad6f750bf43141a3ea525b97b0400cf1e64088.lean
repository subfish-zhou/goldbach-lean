import Wu04BypassMatrix

noncomputable section
namespace WuTarget.W04
open Real Set MeasureTheory NodeExtension ActualNineFeedback
open scoped Interval BigOperators

def eKernel (S : ℝ) (k : Fin 9) : ℝ :=
  ∫ t in (S - 2)..3,
    nineProfile (nodeBasis k) t / t * log ((t + 1) / (S - 1))

def clippedCell (S : ℝ) (k : Fin 9) : ℝ :=
  if S - 2 ≤ upperNode k then
    Wu04Bypass.cell S (max (S - 2) (upperLeft k)) (upperNode k)
  else 0

theorem upperLeft_le_upperNode (k : Fin 9) : upperLeft k ≤ upperNode k := by
  have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  unfold upperLeft upperNode
  split_ifs <;> linarith

theorem basis_profile (k : Fin 9) (t : ℝ) :
    nineProfile (nodeBasis k) t =
      (Ioc (upperLeft k) (upperNode k)).indicator (fun _ => (1 : ℝ)) t := by
  classical
  unfold nineProfile
  rw [Finset.sum_eq_single k]
  · simp [nodeBasis]
  · intro j _ hj
    simp [nodeBasis, hj]
  · simp

theorem kernel_integrand_nonneg {S t : ℝ} (hS : 3 ≤ S) (ht : S - 2 ≤ t)
    (k : Fin 9) :
    0 ≤ nineProfile (nodeBasis k) t / t * log ((t + 1) / (S - 1)) := by
  exact mul_nonneg
    (div_nonneg (nineProfile_nonneg (nodeBasis_nonneg k) t) (by linarith))
    (log_nonneg ((one_le_div (by linarith : 0 < S - 1)).mpr (by linarith)))

theorem eKernel_nonneg {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) (k : Fin 9) :
    0 ≤ eKernel S k :=
  intervalIntegral.integral_nonneg (by linarith)
    (fun t ht => kernel_integrand_nonneg hS ht.1 k)

theorem eKernel_zero_of_right_le {S : ℝ} (hS5 : S ≤ 5) (k : Fin 9)
    (hk : upperNode k ≤ S - 2) : eKernel S k = 0 := by
  unfold eKernel
  calc
    _ = ∫ t in (S - 2)..3, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_uIoo
      intro t ht
      rw [uIoo_of_le (by linarith : S - 2 ≤ 3)] at ht
      have hnot : t ∉ Ioc (upperLeft k) (upperNode k) := by
        intro h
        linarith [ht.1, h.2]
      dsimp only
      rw [basis_profile, indicator_of_notMem hnot]
      simp
    _ = 0 := by simp

theorem clippedCell_zero_of_right_le {S : ℝ} (k : Fin 9)
    (hk : upperNode k ≤ S - 2) : clippedCell S k = 0 := by
  unfold clippedCell
  split_ifs with h
  · have he : S - 2 = upperNode k := le_antisymm h hk
    rw [he, max_eq_left (upperLeft_le_upperNode k)]
    simp [Wu04Bypass.cell]
  · rfl

theorem clippedCell_nonneg (S : ℝ) (k : Fin 9) : 0 ≤ clippedCell S k := by
  unfold clippedCell
  split_ifs with h
  · have ha := le_max_left (S - 2) (upperLeft k)
    have hab := max_le h (upperLeft_le_upperNode k)
    have hb := (upperNode_bounds k).1
    unfold Wu04Bypass.cell
    apply div_nonneg
    · exact mul_nonneg (by linarith) (by linarith)
    · positivity
  · exact le_rfl

theorem clippedCell_le_eKernel {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (k : Fin 9) : clippedCell S k ≤ eKernel S k := by
  unfold clippedCell
  split_ifs with h
  · let a := max (S - 2) (upperLeft k)
    have ha : S - 2 ≤ a := le_max_left _ _
    have hal : upperLeft k ≤ a := le_max_right _ _
    have hab : a ≤ upperNode k := max_le h (upperLeft_le_upperNode k)
    have hi := (profile_subinterval
      (profile_div_integrable (nineProfile_integrable (nodeBasis k)))
      (by linarith : 1 ≤ S - 2) (by linarith : S - 2 ≤ 3)).mul_continuousOn
        (log_weight_continuous hS hS5)
    have he :
        (∫ t in a..upperNode k,
          nineProfile (nodeBasis k) t / t * log ((t + 1) / (S - 1))) =
        ∫ t in a..upperNode k, log ((t + 1) / (S - 1)) / t := by
      apply intervalIntegral.integral_congr_uIoo
      intro t ht
      rw [uIoo_of_le hab] at ht
      dsimp only
      rw [nineProfile_cell (nodeBasis k) ⟨hal.trans_lt ht.1, ht.2.le⟩]
      simp [nodeBasis, div_mul_eq_mul_div]
    have hn : 0 ≤ᵐ[volume.restrict (Ioc (S - 2) 3)]
        (fun t => nineProfile (nodeBasis k) t / t * log ((t + 1) / (S - 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact kernel_integrand_nonneg hS ht.1.le k
    have hm := intervalIntegral.integral_mono_interval ha hab (upperNode_bounds k).2 hn hi
    rw [he] at hm
    exact (Wu04Bypass.cell_le_integral hS ha hab).trans hm
  · exact eKernel_nonneg hS hS5 k

theorem eKernel_le_eProfile {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (k : Fin 9) : eKernel S k ≤ eProfile (nineProfile (nodeBasis k)) S := by
  have ha := (profiles_nonneg
    (fun t _ => nineProfile_nonneg (nodeBasis_nonneg k) t)).1
  have hl : 0 ≤ log (4 / (S - 1)) :=
    log_nonneg ((one_le_div (by linarith : 0 < S - 1)).mpr (by linarith))
  exact le_add_of_nonneg_left (mul_nonneg ha hl)

theorem clippedCell_le_eProfile {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (k : Fin 9) : clippedCell S k ≤ eProfile (nineProfile (nodeBasis k)) S :=
  (clippedCell_le_eKernel hS hS5 k).trans (eKernel_le_eProfile hS hS5 k)

end WuTarget.W04
