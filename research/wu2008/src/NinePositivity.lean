import NineLiteral

namespace NineFeedbackStrength
open Wu2008DoubleSieve ActualNineFeedback NodeExtension Real Set MeasureTheory
open scoped BigOperators Interval
noncomputable section

/-- Positivity of the already paid eight nonterminal original constants. -/
theorem publication_pos {i : Fin 9} (hi : i ≠ 8) : 0 < publication i := by
  revert hi
  refine Fin.addCases (m := 4) (n := 5) (fun j _ => ?_) (fun j hj => ?_) i
  · refine Fin.cases ?_ (fun k => ?_) j
    · norm_num [publication,Wu04CurvePaid.publication]
    · rw [publication_coupled_succ]
      unfold Wu04RemainingCore.publication
      split_ifs <;> norm_num
  · rw [publication_first]
    have hn : j ≠ Fin.last 4 := by
      intro he
      subst j
      exact hj rfl
    obtain ⟨k,rfl⟩ := Fin.eq_castSucc_of_ne_last hn
    have h : ∀ k : Fin 4,0 < Wu04FirstCore.publication k.castSucc := by
      simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,
        Fin.castSucc_zero,Fin.castSucc_succ,Wu04FirstCore.publication,
        Matrix.cons_val_zero,Matrix.cons_val_succ]
      norm_num
    exact h k

theorem base_pos {i : Fin 9} (hi : i ≠ 8) : 0 < base i :=
  (publication_pos hi).trans_le (publication_le_base i)

theorem terminal_feedback (z : Fin 9 → ℝ) :
    feedback z 8 = eProfile (nineProfile z) 3 := by
  change firstFeedback z (firstNode 4) (firstS 4) = _
  have hn : firstNode (4 : Fin 5) = 3 := by norm_num [firstNode]
  rw [hn]
  change eProfile (nineProfile z) 3 + profileJ z 3 3 / 2 = _
  simp [profileJ]

/-- A literal positive entry, proved by its original integral on the original first cell.
No quadrature, sampled point, printed matrix entry, or replacement vector is used. -/
theorem terminal_first_entry_pos : 0 < feedbackMatrix 8 0 := by
  let f : ℝ → ℝ := fun t => nineProfile (nodeBasis 0) t / t * log ((t+1)/2)
  have hw : ContinuousOn (fun t : ℝ => log ((t+1)/2)) (uIcc 1 3) := by
    simpa only [show (3:ℝ)-2=1 by norm_num,show (3:ℝ)-1=2 by norm_num] using
      log_weight_continuous (v := 3) (by norm_num) (by norm_num)
  have hfi : IntervalIntegrable f volume 1 3 :=
    (profile_div_integrable (nineProfile_integrable (nodeBasis 0))).mul_continuousOn hw
  have hn (t : ℝ) (ht : t ∈ Icc 1 3) : 0 ≤ f t := by
    exact mul_nonneg (div_nonneg (nineProfile_nonneg (nodeBasis_nonneg 0) t)
      (by linarith [ht.1])) (log_nonneg (by linarith [ht.1]))
  have hfirst : IntervalIntegrable f volume 1 (upperNode 0) := by
    apply hfi.mono_set
    rw [uIcc_of_le (by norm_num [upperNode] : (1:ℝ) ≤ upperNode 0),uIcc_of_le (by norm_num : (1:ℝ)≤3)]
    exact Icc_subset_Icc le_rfl (upperNode_bounds 0).2
  have hp : 0 < ∫ t in (1:ℝ)..(upperNode 0), f t := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hfirst
    · intro t ht
      have hcell : t ∈ Ioc (upperLeft 0) (upperNode 0) := ⟨ht.1,ht.2.le⟩
      dsimp [f]
      rw [nineProfile_cell _ hcell]
      change 0 < (1:ℝ)/t * log ((t+1)/2)
      exact mul_pos (div_pos (by norm_num) (by linarith [ht.1])) (log_pos (by linarith [ht.1]))
    · norm_num [upperNode]
  have hm : (∫ t in (1:ℝ)..(upperNode 0),f t) ≤ ∫ t in (1:ℝ)..3,f t := by
    apply intervalIntegral.integral_mono_interval le_rfl (upperNode_bounds 0).1 (upperNode_bounds 0).2 _ hfi
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall
      (fun t ht => hn t ⟨ht.1.le,ht.2⟩))
  have ha := (profiles_nonneg (fun t _ => nineProfile_nonneg (nodeBasis_nonneg 0) t)).1
  have hlog : 0 ≤ log ((4:ℝ)/2) := log_nonneg (by norm_num)
  change 0 < feedback (nodeBasis 0) 8
  rw [terminal_feedback]
  simp only [eProfile,show (3:ℝ)-1=2 by norm_num,show (3:ℝ)-2=1 by norm_num]
  change 0 < aProfile (nineProfile (nodeBasis 0))*log (4/2) + ∫ t in (1:ℝ)..3,f t
  exact add_pos_of_nonneg_of_pos (mul_nonneg ha hlog) (hp.trans_le hm)

theorem Ainf_pos (i : Fin 9) : 0 < FeedbackLimit.Ainf i := by
  by_cases hi : i=8
  · subst i
    have h0 : 0 < FeedbackLimit.Ainf 0 :=
      (publication_pos (by decide : (0 : Fin 9)≠8)).trans_le (publication_le_Ainf 0)
    have hs : feedbackMatrix 8 0 * FeedbackLimit.Ainf 0 ≤
        matrixApply feedbackMatrix FeedbackLimit.Ainf 8 :=
      Finset.single_le_sum (fun k _ => mul_nonneg (feedbackMatrix_nonneg 8 k) (FeedbackLimit.Ainf_nonneg k))
        (Finset.mem_univ 0)
    rw [Ainf_affine]
    exact (mul_pos terminal_first_entry_pos h0).trans_le
      (hs.trans (le_add_of_nonneg_left (base_nonneg 8)))
  · exact (publication_pos hi).trans_le (publication_le_Ainf i)

/-- Strict diagonal control follows from the genuine positive forcing, not a numerical entry bound. -/
theorem terminal_diagonal_lt_one : feedbackMatrix 8 8 < 1 := by
  have hs : feedbackMatrix 8 8 * FeedbackLimit.Ainf 8 <
      matrixApply feedbackMatrix FeedbackLimit.Ainf 8 := by
    exact Finset.single_lt_sum (by decide : (0 : Fin 9)≠8)
      (Finset.mem_univ 8) (Finset.mem_univ 0)
      (mul_pos terminal_first_entry_pos (Ainf_pos 0))
      (fun k _ _ => mul_nonneg (feedbackMatrix_nonneg 8 k) (FeedbackLimit.Ainf_nonneg k))
  have he := Ainf_affine 8
  have hb : base (8 : Fin 9)=0 := rfl
  rw [hb,zero_add] at he
  rw [← he] at hs
  nlinarith only [hs,Ainf_pos 8]

end
end NineFeedbackStrength
