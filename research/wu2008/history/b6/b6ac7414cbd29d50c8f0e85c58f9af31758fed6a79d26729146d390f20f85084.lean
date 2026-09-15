import WRMapMSigmaRoot
import WRMapMMatrixSelectedChange

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open WuPaper.RMapMSigma
open scoped Interval

def JKernel (s S t : ℝ) : ℝ :=
  log ((S - 1) / (s - 1)) *
    (sigma0 t + (Icc (S - 2) 3).indicator (fun _ => (1 : ℝ)) t) / t +
  (Icc (S - S / s - 1) (S - 2)).indicator (fun _ => (1 : ℝ)) t / t *
    log ((t + 1) / ((s - 1) * (S - 1 - t)))

def Xi1 (s S t : ℝ) : ℝ :=
  sigma0 t / (2 * t) * log (16 / ((s - 1) * (S - 1))) +
  (Icc (S - 2) 3).indicator (fun _ => (1 : ℝ)) t / (2 * t) *
    log ((t + 1) ^ 2 / ((s - 1) * (S - 1))) +
  (Icc (S - S / s - 1) (S - 2)).indicator (fun _ => (1 : ℝ)) t / (2 * t) *
    log ((t + 1) / ((s - 1) * (S - 1 - t)))

theorem J_endpoints {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s < S) (hr : 2 ≤ S - S / s) :
    0 < 1 - 1 / s ∧ 1 - 1 / s < 1 - 1 / S ∧ 1 - 1 / S < 1 ∧
    2 ≤ (1 - 1 / s) * S ∧ (1 - 1 / S) * S ≤ 4 := by
  have hs0 : 0 < s := by linarith
  have hS0 : 0 < S := by linarith
  have hsinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs
  have hi := one_div_lt_one_div_of_lt hs0 hsS
  have he : (1 - 1 / S) * S = S - 1 := by field_simp
  have he' : (1 - 1 / s) * S = S - S / s := by ring
  rw [he, he']
  exact ⟨by linarith, by linarith, by linarith [one_div_pos.mpr hS0], hr,
    by linarith⟩

theorem J_source_logs {s S t : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) :
    ((1 - 1 / S) - (1 - 1 / s) * (1 - 1 / S)) /
        ((1 - 1 / s) - (1 - 1 / s) * (1 - 1 / S)) = (S - 1) / (s - 1) ∧
    (1 - (1 - 1 / s)) * (t + 1) /
        ((1 - 1 / s) * (S - 1 - t)) =
      (t + 1) / ((s - 1) * (S - 1 - t)) := by
  have hs0 : s ≠ 0 := by linarith
  have hS0 : S ≠ 0 := by linarith
  have hs1 : s - 1 ≠ 0 := by linarith
  constructor
  · field_simp
    ring
  · rw [show 1 - (1 - 1 / s) = 1 / s by ring,
      show 1 - 1 / s = (s - 1) / s by field_simp]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    calc
      _ = (s⁻¹ * s) * ((t + 1) * ((S - 1 - t)⁻¹ * (s - 1)⁻¹)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hs0, one_mul]

theorem J_source_identity {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s < S) (hr : 2 ≤ S - S / s) :
    IntervalIntegrable (fun t => f t * JKernel s S t) volume 1 3 ∧
    (∫ t in (1 : ℝ)..3, f t * JKernel s S t) =
      source63RHS f (1 - 1 / s) (1 - 1 / S) S := by
  have hg := J_endpoints hs hS hS5 hsS hr
  have hi := lemma63_second_integrable hf hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2
  have hs0 : s ≠ 0 := by linarith
  have hS0 : S ≠ 0 := by linarith
  have he : (1 - 1 / S) * S - 1 = S - 2 := by field_simp; ring
  have he' : (1 - 1 / s) * S - 1 = S - S / s - 1 := by ring
  have hb : IntervalIntegrable (fun t =>
      f t * (sigma0 t + (Icc (S - 2) 3).indicator (fun _ => (1 : ℝ)) t) / t)
      volume 1 3 := by
    have hind' : IntervalIntegrable
        ((Icc (S - 2) 3).indicator (fun t => f t / t)) volume 1 3 := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le
        (by norm_num : (1 : ℝ) ≤ 3)).mpr
      exact ((intervalIntegrable_iff_integrableOn_Icc_of_le
        (by norm_num : (1 : ℝ) ≤ 3)).mp
        (profile_div_integrable hf)).indicator measurableSet_Icc
    convert (sigma_weight_integrable hf).add hind' using 1
    ext t
    by_cases ht : t ∈ Icc (S - 2) 3 <;> simp [ht]
    ring
  have hpoint (t : ℝ) :
      f t * JKernel s S t =
      log ((S - 1) / (s - 1)) *
        (f t * (sigma0 t + (Icc (S - 2) 3).indicator (fun _ => (1 : ℝ)) t) / t) +
      f t * (Icc (S - S / s - 1) (S - 2)).indicator (fun _ => (1 : ℝ)) t / t *
        log ((t + 1) / ((s - 1) * (S - 1 - t))) := by
    dsimp [JKernel]
    ring
  have hlog (t : ℝ) := (J_source_logs (t := t) hs hS).2
  simp_rw [he, he', hlog] at hi
  constructor
  · exact ((hb.const_mul _).add hi).congr (fun t _ => (hpoint t).symm)
  · simp_rw [hpoint]
    rw [intervalIntegral.integral_add (hb.const_mul _) hi,
      intervalIntegral.integral_const_mul]
    unfold source63RHS
    simp_rw [he, he', hlog]
    rw [(J_source_logs (t := 0) hs hS).1]

theorem Xi1_kernel_identity {s S t : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S)
    (ht : t ∈ Icc 1 3) :
    Xi1 s S t = upperKernel S t + JKernel s S t / 2 := by
  have hs1 : s - 1 ≠ 0 := by linarith
  have hS1 : S - 1 ≠ 0 := by linarith
  have ht1 : t + 1 ≠ 0 := by linarith [ht.1]
  have h16 : log (16 : ℝ) = 2 * log 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, log_pow]
    norm_num
  simp only [Xi1, JKernel, upperKernel,
    log_div (by norm_num : (16 : ℝ) ≠ 0) (mul_ne_zero hs1 hS1),
    log_div (pow_ne_zero 2 ht1) (mul_ne_zero hs1 hS1),
    log_div (by norm_num : (4 : ℝ) ≠ 0) hS1,
    log_div ht1 hS1, log_div hS1 hs1, log_mul hs1 hS1,
    log_pow, h16]
  push_cast
  ring

theorem Xi1_integral_identity {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s < S) (hr : 2 ≤ S - S / s) :
    IntervalIntegrable (fun t => f t * Xi1 s S t) volume 1 3 ∧
    (∫ t in (1 : ℝ)..3, f t * Xi1 s S t) =
      eProfile f S + source63RHS f (1 - 1 / s) (1 - 1 / S) S / 2 := by
  have hj := J_source_identity hf hs hS hS5 hsS hr
  have hu := upperKernel_integrable hf ⟨hS, hS5⟩
  have he (t : ℝ) (ht : t ∈ uIcc 1 3) :
      f t * Xi1 s S t = f t * upperKernel S t + (f t * JKernel s S t) / 2 := by
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
    rw [Xi1_kernel_identity hs hS ht]
    ring
  constructor
  · exact (hu.add (hj.1.div_const 2)).congr (fun t ht => (he t (uIoc_subset_uIcc ht)).symm)
  · rw [intervalIntegral.integral_congr he,
      intervalIntegral.integral_add hu (hj.1.div_const 2),
      intervalIntegral.integral_div, upperKernel_identity hf ⟨hS, hS5⟩, hj.2]

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))

#check @Wu2008DoubleSieve.wuImprovementLimit_firstFunctionalGain_source
