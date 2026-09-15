import R2MatrixXi1

noncomputable section
namespace WuPaper.R2Matrix
open Real Set MeasureTheory NodeExtension ActualNineFeedback Wu2008DoubleSieve
open WuPaper.RMapMSigma
open scoped Interval BigOperators

def firstJKernel (s S t : ℝ) : ℝ :=
  (sigma0 t + (Icc (S - 2) 3).indicator (fun _ => (1 : ℝ)) t) / t *
    log ((S - 1) / (s - 1)) +
  (Icc (S - S / s - 1) (S - 2)).indicator (fun _ => (1 : ℝ)) t / t *
    log ((t + 1) / ((s - 1) * (S - 1 - t)))

theorem first_log_combination {s S x : ℝ} (hs : 1 < s) (hS : 1 < S) (hx : 0 < x) :
    log (x^2 / ((s - 1) * (S - 1))) =
      2 * log (x / (S - 1)) + log ((S - 1) / (s - 1)) := by
  have hs1 : s - 1 ≠ 0 := by linarith
  have hS1 : S - 1 ≠ 0 := by linarith
  rw [log_div (pow_ne_zero 2 hx.ne') (mul_ne_zero hs1 hS1), log_pow,
    log_mul hs1 hS1, log_div hx.ne' hS1, log_div hS1 hs1]
  ring

theorem xi1_split_original (i : Fin 5) {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 3) :
    Wu04Source.xi1 t (firstNode i) (firstS i) =
      upperKernel (firstS i) t + firstJKernel (firstNode i) (firstS i) t / 2 := by
  have hg := first_geometry i
  have hs : 1 < firstNode i := by linarith [hg.1]
  have hS : 1 < firstS i := by linarith [hg.2.2.1]
  have h4 := first_log_combination hs hS (by norm_num : (0 : ℝ) < 4)
  norm_num only [show (4 : ℝ)^2 = 16 by norm_num] at h4
  have htlog := first_log_combination hs hS (by linarith [ht.1] : 0 < t + 1)
  unfold Wu04Source.xi1 upperKernel firstJKernel
  rw [h4, htlog]
  simp only [Wu04Source.paperSigma0_eq, Wu04Source.alpha2, Wu04Source.alpha3]
  ring

theorem first_source63_endpoints {s S : ℝ} (_hs : 0 < s) (hS : 0 < S) :
    (1 - 1 / s) * S - 1 = S - S / s - 1 ∧
    (1 - 1 / S) * S - 1 = S - 2 := by
  constructor
  · ring
  · field_simp
    ring

theorem first_source63_log {s S : ℝ} (hs : 1 < s) (hS : 1 < S) :
    log (((1 - 1 / S) - (1 - 1 / s) * (1 - 1 / S)) /
      ((1 - 1 / s) - (1 - 1 / s) * (1 - 1 / S))) =
        log ((S - 1) / (s - 1)) := by
  congr 1
  have hs0 : s ≠ 0 := by linarith
  have hS0 : S ≠ 0 := by linarith
  have hs1 : s - 1 ≠ 0 := by linarith
  have hd : (1 - 1 / s) - (1 - 1 / s) * (1 - 1 / S) ≠ 0 := by
    have ha : 0 < 1 - 1 / s := by
      apply sub_pos.mpr
      exact (div_lt_one (by linarith : 0 < s)).mpr hs
    have he : (1 - 1 / s) - (1 - 1 / s) * (1 - 1 / S) = (1 - 1 / s) / S := by ring
    rw [he]
    exact (div_pos ha (by linarith)).ne'
  field_simp
  ring

theorem first_source63_partial_log {s S t : ℝ} (hs : 1 < s) :
    log ((1 - (1 - 1 / s)) * (t + 1) /
      ((1 - 1 / s) * (S - 1 - t))) =
      log ((t + 1) / ((s - 1) * (S - 1 - t))) := by
  congr 1
  have hs0 : s ≠ 0 := by linarith
  have hs1 : s - 1 ≠ 0 := by linarith
  by_cases ht : S - 1 - t = 0
  · simp [ht]
  · have ha : 1 - 1 / s ≠ 0 := by
      have ha : 0 < 1 - 1 / s :=
        sub_pos.mpr ((div_lt_one (by linarith : 0 < s)).mpr hs)
      exact ha.ne'
    field_simp
    ring

theorem first_source63_geometry (i : Fin 5) (hi : i.val < 4) :
    0 < 1 - 1 / firstNode i ∧
    1 - 1 / firstNode i < 1 - 1 / firstS i ∧
    1 - 1 / firstS i < 1 ∧
    2 ≤ (1 - 1 / firstNode i) * firstS i ∧
    (1 - 1 / firstS i) * firstS i ≤ 4 := by
  fin_cases i <;> norm_num [firstNode, firstS] at *

theorem source63_first_integral (i : Fin 5) (hi : i.val < 4) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 1 3) :
    source63RHS f (1 - 1 / firstNode i) (1 - 1 / firstS i) (firstS i) =
      ∫ t in (1 : ℝ)..3, f t * firstJKernel (firstNode i) (firstS i) t := by
  let s := firstNode i
  let S := firstS i
  let a := 1 - 1 / s
  let b := 1 - 1 / S
  have hg := first_source63_geometry i hi
  have hgeo := first_geometry i
  have hs : 1 < s := by linarith [hgeo.1]
  have hS : 1 < S := by linarith [hgeo.2.2.1]
  have he := first_source63_endpoints (by linarith : 0 < s) (by linarith : 0 < S)
  have hpart := lemma63_second_integrable hf hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2
  have htail : IntervalIntegrable ((Icc (b * S - 1) 3).indicator (fun t => f t / t))
      volume 1 3 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 3)).mpr
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (1 : ℝ) ≤ 3)).mp (profile_div_integrable hf)).indicator measurableSet_Icc
  have hbase : IntervalIntegrable
      (fun t => f t * (sigma0 t + (Icc (b * S - 1) 3).indicator (fun _ => (1 : ℝ)) t) / t)
      volume 1 3 := by
    convert (sigma_weight_integrable hf).add htail using 1
    ext t
    by_cases ht : t ∈ Icc (b * S - 1) 3 <;> simp [ht] <;> ring
  have hpoint (t : ℝ) :
      f t * firstJKernel s S t =
      log ((b - a * b) / (a - a * b)) *
        (f t * (sigma0 t + (Icc (b * S - 1) 3).indicator (fun _ => (1 : ℝ)) t) / t) +
      f t * (Icc (a * S - 1) (b * S - 1)).indicator (fun _ => (1 : ℝ)) t / t *
        log ((1 - a) * (t + 1) / (a * (S - 1 - t))) := by
    dsimp [a, b]
    rw [he.1, he.2, first_source63_log hs hS, first_source63_partial_log hs]
    unfold firstJKernel
    ring
  change source63RHS f a b S =
    ∫ t in (1 : ℝ)..3, f t * firstJKernel s S t
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add (hbase.const_mul _) hpart,
    intervalIntegral.integral_const_mul]
  rfl

theorem profileJ_original_integral (i : Fin 5) (hi : i.val < 4) (z : Fin 9 → ℝ) :
    profileJ z (firstNode i) (firstS i) =
      ∫ t in (1 : ℝ)..3, nineProfile z t * firstJKernel (firstNode i) (firstS i) t := by
  have hg := first_source63_geometry i hi
  have hS : 0 < firstS i := by have h := (first_geometry i).2.2.1; linarith
  unfold profileJ
  rw [rationalWeight_rescale hg.1 hg.2.1 hg.2.2.1 hS]
  rw [(gProfile_weighted_formula (nineProfile_integrable z) hg.1 hg.2.1
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2).2]
  exact source63_first_integral i hi (nineProfile_integrable z)

theorem firstFeedback_eq_original_integral (i : Fin 5) (z : Fin 9 → ℝ) :
    firstFeedback z (firstNode i) (firstS i) =
      ∫ t in (1 : ℝ)..3, nineProfile z t * Wu04Source.xi1 t (firstNode i) (firstS i) := by
  by_cases hi : i.val < 4
  · have hgeo := first_geometry i
    have hU := upperKernel_integrable (nineProfile_integrable z) ⟨hgeo.2.2.1, hgeo.2.2.2.1⟩
    have hJ : IntervalIntegrable
        (fun t => nineProfile z t * firstJKernel (firstNode i) (firstS i) t)
        volume 1 3 := by
      apply (((xi1_weighted_integrable i (nineProfile_integrable z)).sub hU).const_mul 2).congr
      intro t ht
      have ht' : t ∈ Icc (1 : ℝ) 3 := by
        simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] using uIoc_subset_uIcc ht
      dsimp only
      rw [xi1_split_original i ht']
      ring
    have he :
        (∫ t in (1 : ℝ)..3, nineProfile z t * Wu04Source.xi1 t (firstNode i) (firstS i)) =
        (∫ t in (1 : ℝ)..3,
          nineProfile z t * upperKernel (firstS i) t +
          (nineProfile z t * firstJKernel (firstNode i) (firstS i) t) / 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
      dsimp only
      rw [xi1_split_original i ht]
      ring
    rw [he, intervalIntegral.integral_add hU (hJ.div_const 2),
      intervalIntegral.integral_div,
      upperKernel_identity (nineProfile_integrable z) ⟨hgeo.2.2.1, hgeo.2.2.2.1⟩,
      ← profileJ_original_integral i hi z]
    rfl
  · have he : i = (4 : Fin 5) := Fin.ext (by omega)
    subst i
    rw [show firstNode (4 : Fin 5) = 3 by norm_num [firstNode],
      show firstS (4 : Fin 5) = 3 from rfl]
    exact Wu04Source.firstFeedback_eq_paper_integral z

theorem first_original_matrix_entries (i : Fin 5) (k : Fin 9) :
    feedbackMatrix ⟨i.val + 4, by omega⟩ k =
      ∫ t in Wu04Source.paperNode k.val..Wu04Source.paperNode (k.val + 1),
        Wu04Source.xi1 t (firstNode i) (firstS i) := by
  have hrow : feedbackMatrix ⟨i.val + 4, by omega⟩ k =
      firstFeedback (nodeBasis k) (firstNode i) (firstS i) := by
    simp [feedbackMatrix, feedback]
  rw [hrow, firstFeedback_eq_original_integral]
  exact original_basis_coefficient k (xi1_integrable i)

end WuPaper.R2Matrix

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Matrix then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
