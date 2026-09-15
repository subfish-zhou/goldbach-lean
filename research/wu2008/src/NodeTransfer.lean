import NodeTwentyOne

namespace NodeExtension
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval BigOperators

noncomputable def nodeBasis (k : Fin 9) (i : Fin 9) : ℝ := if i = k then 1 else 0

theorem nodeBasis_nonneg (k i : Fin 9) : 0 ≤ nodeBasis k i := by
  unfold nodeBasis
  split_ifs <;> norm_num

theorem nineProfile_basis (k : Fin 9) (t : ℝ) :
    nineProfile (nodeBasis k) t = (Ioc (upperLeft k) (upperNode k)).indicator (fun _ => 1) t := by
  classical
  unfold nineProfile
  rw [Finset.sum_eq_single k]
  · simp [nodeBasis]
  · intro i _ hik
    simp only [nodeBasis, if_neg hik, indicator_zero]
  · simp

theorem nineProfile_expansion (z : Fin 9 → ℝ) (t : ℝ) :
    nineProfile z t = ∑ k : Fin 9, z k * nineProfile (nodeBasis k) t := by
  classical
  unfold nineProfile
  apply Finset.sum_congr rfl
  intro k _
  rw [← nineProfile, nineProfile_basis]
  by_cases ht : t ∈ Ioc (upperLeft k) (upperNode k)
  · simp only [indicator_of_mem ht, mul_one]
  · simp only [indicator_of_notMem ht, mul_zero]

/-- Finite expansion of an integrable profile against a continuous compact-interval weight. -/
theorem weighted_profile_expansion (z : Fin 9 → ℝ) {a : ℝ} (ha : 1 ≤ a) (ha3 : a ≤ 3)
    {w : ℝ → ℝ} (hw : ContinuousOn w (uIcc a 3)) :
    (∫ t in a..3, nineProfile z t * w t) =
      ∑ k : Fin 9, z k * ∫ t in a..3, nineProfile (nodeBasis k) t * w t := by
  have hpoint (t : ℝ) : nineProfile z t * w t =
      ∑ k : Fin 9, z k * (nineProfile (nodeBasis k) t * w t) := by
    rw [nineProfile_expansion, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul]
  · intro k _
    exact ((profile_subinterval (nineProfile_integrable _) ha ha3).mul_continuousOn hw).const_mul _

noncomputable def logMoment (z : Fin 9 → ℝ) (v : ℝ) : ℝ :=
  ∫ t in (v - 2)..3, nineProfile z t / t * log ((t + 1) / (v - 1))

theorem logMoment_expansion (z : Fin 9 → ℝ) {v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    logMoment z v = ∑ k : Fin 9, z k * logMoment (nodeBasis k) v := by
  have hw := (reciprocal_continuous (by linarith : 0 < v - 2)
    (by linarith : v - 2 ≤ 3)).mul (log_weight_continuous hv hv5)
  have h := weighted_profile_expansion z (by linarith : 1 ≤ v - 2)
    (by linarith : v - 2 ≤ 3) hw
  simpa only [logMoment, Pi.mul_apply, ← mul_assoc, mul_one_div] using h

theorem aProfile_feedback_form (z : Fin 9 → ℝ) :
    aProfile (nineProfile z) = (∫ v in (3 : ℝ)..5, logMoment z v / v) / (1 - D0) := by
  rw [aProfile_eq, ← (sigma_feedback (profile_div_integrable (nineProfile_integrable z))).2]
  rfl

theorem aProfile_expansion (z : Fin 9 → ℝ) :
    aProfile (nineProfile z) = ∑ k : Fin 9, z k * aProfile (nineProfile (nodeBasis k)) := by
  rw [aProfile_feedback_form]
  have he : (∫ v in (3 : ℝ)..5, logMoment z v / v) =
      ∫ v in (3 : ℝ)..5, ∑ k : Fin 9, z k * (logMoment (nodeBasis k) v / v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] at hv
    dsimp only
    rw [logMoment_expansion z hv.1 hv.2, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul, Finset.sum_div, aProfile_feedback_form,
      mul_div_assoc]
  · intro k _
    exact (sigma_feedback (profile_div_integrable (nineProfile_integrable (nodeBasis k)))).1.const_mul _

theorem eProfile_expansion (z : Fin 9 → ℝ) {v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    eProfile (nineProfile z) v =
      ∑ k : Fin 9, z k * eProfile (nineProfile (nodeBasis k)) v := by
  change aProfile (nineProfile z) * _ + logMoment z v = _
  rw [aProfile_expansion, logMoment_expansion z hv hv5, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  dsimp [eProfile, logMoment]
  ring

theorem extendedNode_expansion (z : Fin 9 → ℝ) {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) :
    extendedNode z i = ∑ k : Fin 9, z k * extendedNode (nodeBasis k) i := by
  classical
  by_cases h : 2 ≤ i ∧ i ≤ 10
  · simp only [extendedNode, dif_pos h, nodeBasis]
    simp
  · simp only [extendedNode, dif_neg h]
    apply eProfile_expansion
    · have hh := rNode_mono (show 10 ≤ i by omega)
      norm_num [rNode] at hh
      exact hh
    · exact (rNode_bounds hi29).2

/-- The literal 21 by 9 matrix: evaluate the original expression on each coordinate vector. -/
noncomputable def transferMatrix (j : Fin 21) (k : Fin 9) : ℝ :=
  originalTransfer (nodeBasis k) (j.val + 1)

theorem transferMatrix_nonneg (j : Fin 21) (k : Fin 9) : 0 ≤ transferMatrix j k :=
  originalTransfer_nonneg (nodeBasis_nonneg k) (by omega) (by omega)

theorem originalTransfer_expansion (z : Fin 9 → ℝ) (j : Fin 21) :
    originalTransfer z (j.val + 1) = ∑ k : Fin 9, transferMatrix j k * z k := by
  classical
  simp only [transferMatrix, originalTransfer]
  simp only [Finset.sum_mul, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp [nodeBasis, mul_comm]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hit
    have hh := Finset.mem_Icc.mp hit
    rw [extendedNode_expansion z (by omega) hh.2, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem actual_twentyone_matrix {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10) (j : Fin 21) :
    (∑ k : Fin 9, transferMatrix j k * actualNine δ k) ≤
      wuImprovementLimit false δ (rNode (j.val + 1)) := by
  rw [← originalTransfer_expansion]
  exact actual_twentyone hd hdhi j

end NodeExtension
