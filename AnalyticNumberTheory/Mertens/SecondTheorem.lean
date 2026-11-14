module

public import AnalyticNumberTheory.Mertens.Basic
public import AnalyticNumberTheory.Mertens.FirstTheorem
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Mertens' second theorem

Abel summation with weight `1 / log t` turns Mertens' first theorem into the
reciprocal-prime asymptotic. The remainder is a bounded endpoint term divided
by `log x` and a tail against the integrable kernel `1 / (t * log² t)`.
-/

@[expose] public section

namespace AnalyticNumberTheory.Mertens

open Asymptotics Filter Finset MeasureTheory Real

/-- A reusable improper-integral tail estimate for the kernel that occurs in
the Mertens error term. -/
theorem norm_integral_Ioi_le_div_log {f : ℝ → ℝ} {x C : ℝ} (hx : 1 < x)
    (hbound : ∀ t ∈ Set.Ioi x, ‖f t‖ ≤ C * (t⁻¹ / (log t) ^ 2)) :
    ‖∫ t in Set.Ioi x, f t‖ ≤ C / log x := by
  have hk : IntegrableOn (fun t : ℝ => t⁻¹ / (log t) ^ 2) (Set.Ioi x) volume :=
    integrableOn_inv_div_log_sq_Ioi hx
  have hCk : IntegrableOn (fun t : ℝ => C * (t⁻¹ / (log t) ^ 2)) (Set.Ioi x) volume :=
    hk.const_mul C
  calc
    ‖∫ t in Set.Ioi x, f t‖ ≤ ∫ t in Set.Ioi x, C * (t⁻¹ / (log t) ^ 2) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hCk
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbound t ht
    _ = C * ∫ t in Set.Ioi x, t⁻¹ / (log t) ^ 2 := by rw [integral_const_mul]
    _ = C / log x := by rw [integral_inv_div_log_sq_Ioi hx]; ring

private noncomputable def logPrimeCoeff (p : ℕ) : ℝ :=
  if p.Prime then log p / p else 0

private noncomputable def logPrimeSum (x : ℝ) : ℝ :=
  ∑ p ∈ Icc 0 ⌊x⌋₊, logPrimeCoeff p

private theorem logPrimeSum_eq (x : ℝ) :
    logPrimeSum x = ∑ p ∈ ⌊x⌋₊.primesLE, log p / p := by
  rw [logPrimeSum, Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  rfl

private noncomputable def firstError (x : ℝ) : ℝ := logPrimeSum x - log x

private noncomputable def secondKernel (t : ℝ) : ℝ := firstError t * (t⁻¹ / (log t) ^ 2)

private theorem firstError_bounded : ∃ C > 0, ∀ x : ℝ, 1 ≤ x → |firstError x| ≤ C := by
  simp only [firstError, logPrimeSum_eq]
  exact mertensFirst

private theorem locallyIntegrableOn_logPrimeSum :
    LocallyIntegrableOn logPrimeSum (Set.Ici 2) volume := by
  unfold logPrimeSum
  simpa only [one_mul] using
    locallyIntegrableOn_mul_sum_Icc logPrimeCoeff (by norm_num : (0 : ℝ) ≤ 2)
      (locallyIntegrableOn_const (1 : ℝ))

private theorem log_ne_zero_of_two_le {t : ℝ} (ht : 2 ≤ t) : log t ≠ 0 :=
  (log_pos (by linarith)).ne'

private theorem continuousOn_inv_div_log_sq :
    ContinuousOn (fun t : ℝ => t⁻¹ / log t ^ 2) (Set.Ici 2) := by
  have hlog : ContinuousOn log (Set.Ici (2 : ℝ)) := fun t ht =>
    (continuousAt_log (zero_lt_two.trans_le ht).ne').continuousWithinAt
  exact ((continuousOn_id' _).inv₀ fun _ ht => (zero_lt_two.trans_le ht).ne').div
    (hlog.pow 2) fun _ ht => pow_ne_zero 2 (log_ne_zero_of_two_le ht)

private theorem norm_secondKernel_le {C t : ℝ} (ht : 2 ≤ t)
    (hC : |firstError t| ≤ C) : ‖secondKernel t‖ ≤ C * (t⁻¹ / log t ^ 2) := by
  have ht0 : 0 ≤ t := by linarith
  have hq : 0 ≤ t⁻¹ / log t ^ 2 := by positivity
  rw [secondKernel, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq]
  exact mul_le_mul_of_nonneg_right hC hq

private theorem integrableOn_secondKernel :
    IntegrableOn secondKernel (Set.Ioi 2) volume := by
  obtain ⟨C, _, hbound⟩ := firstError_bounded
  have hlog : ContinuousOn log (Set.Ici (2 : ℝ)) := fun t ht =>
    (continuousAt_log (zero_lt_two.trans_le ht).ne').continuousWithinAt
  have hlocal : LocallyIntegrableOn secondKernel (Set.Ici 2) volume := by
    exact (locallyIntegrableOn_logPrimeSum.sub
      (hlog.locallyIntegrableOn measurableSet_Ici)).mul_continuousOn
        continuousOn_inv_div_log_sq isLocallyClosed_Ici
  have hmajorant := (integrableOn_inv_div_log_sq_Ioi (by norm_num : (1 : ℝ) < 2)).const_mul C
  apply Integrable.mono' hmajorant
    (hlocal.aestronglyMeasurable.mono_set Set.Ioi_subset_Ici_self)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_secondKernel_le ht.le (hbound t (one_le_two.trans ht.le))

/-- The Meissel–Mertens constant, obtained by integrating the bounded remainder
in Mertens' first theorem. -/
@[no_expose] noncomputable def mertensSecondConstant : ℝ :=
  1 - log (log 2) + ∫ t in Set.Ioi (2 : ℝ), secondKernel t

private theorem primeReciprocalSum_eq_abel {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ = logPrimeSum x / log x +
      ∫ t in 2..x, (t⁻¹ / log t ^ 2) * logPrimeSum t := by
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc (2 : ℝ) x) :
      DifferentiableAt ℝ (fun t : ℝ => (log t)⁻¹) t :=
    (differentiableAt_log_iff.mpr (zero_lt_two.trans_le ht.1).ne').inv
      (log_ne_zero_of_two_le ht.1)
  have hd_int : IntegrableOn (deriv (fun t : ℝ => (log t)⁻¹)) (Set.Icc 2 x) volume := by
    rw [Real.deriv_inv_log]
    have hcont : ContinuousOn (fun t : ℝ => -(t⁻¹ / log t ^ 2)) (Set.Icc 2 x) :=
      (continuousOn_inv_div_log_sq.mono Set.Icc_subset_Ici_self).neg
    simpa only [neg_div] using hcont.integrableOn_Icc
  rw [primeReciprocalSum, primesUpTo, Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  calc
    _ = ∑ p ∈ Icc 0 ⌊x⌋₊, (log p)⁻¹ * logPrimeCoeff p := by
      apply sum_congr rfl
      intro p _
      unfold logPrimeCoeff
      split_ifs with hp
      · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        field_simp [log_ne_zero_of_two_le hp2]
      · rw [mul_zero]
    _ = _ := by
      rw [sum_mul_eq_sub_integral_mul₁ logPrimeCoeff
        (f := fun t : ℝ => (log t)⁻¹) (by simp [logPrimeCoeff]) (by simp [logPrimeCoeff])
        x hdiff hd_int, ← intervalIntegral.integral_of_le hx, Real.deriv_inv_log]
      change (log x)⁻¹ * logPrimeSum x -
        (∫ t in 2..x, (-t⁻¹ / log t ^ 2) * logPrimeSum t) = _
      simp only [neg_mul, intervalIntegral.integral_neg, sub_neg_eq_add,
        div_eq_mul_inv, mul_comm (log x)⁻¹]

private theorem mertensSecond_remainder {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant) =
      firstError x / log x - ∫ t in Set.Ioi x, secondKernel t := by
  have hx1 : 1 < x := by linarith
  have hmain : IntervalIntegrable (fun t : ℝ => t⁻¹ / log t) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    have ht (t : ℝ) (ht : t ∈ Set.Icc (2 : ℝ) x) : t ≠ 0 :=
      (zero_lt_two.trans_le ht.1).ne'
    have hl (t : ℝ) (ht : t ∈ Set.Icc (2 : ℝ) x) : log t ≠ 0 :=
      log_ne_zero_of_two_le ht.1
    fun_prop (disch := solve_by_elim)
  have herr : IntervalIntegrable secondKernel volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
    exact integrableOn_secondKernel.mono_set Set.Ioc_subset_Ioi_self
  have hsplit :
      (∫ t in 2..x, (t⁻¹ / log t ^ 2) * logPrimeSum t) =
        (∫ t in 2..x, t⁻¹ / log t) + ∫ t in 2..x, secondKernel t := by
    rw [← intervalIntegral.integral_add hmain herr]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    simp only [secondKernel, firstError]
    field_simp [log_ne_zero_of_two_le ht.1]
    ring
  have htail := intervalIntegral.integral_Ioi_sub_Ioi integrableOn_secondKernel hx
  have hend : logPrimeSum x / log x = firstError x / log x + 1 := by
    rw [firstError, sub_div, div_self (log_ne_zero_of_two_le hx)]
    ring
  rw [primeReciprocalSum_eq_abel hx, hsplit, hend,
    integral_inv_div_log (by norm_num) hx1, mertensSecondConstant]
  linarith

private theorem mertensSecond_bound :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
      |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤ C / log x := by
  obtain ⟨C, hC, hbound⟩ := firstError_bounded
  refine ⟨C + C, add_pos hC hC, fun x hx => ?_⟩
  have hx1 : 1 < x := by linarith
  have hlog := log_pos hx1
  have htail := norm_integral_Ioi_le_div_log hx1 fun t ht =>
    norm_secondKernel_le (hx.trans ht.le) (hbound t (hx1.le.trans ht.le))
  rw [mertensSecond_remainder hx]
  calc
    _ ≤ |firstError x / log x| + |∫ t in Set.Ioi x, secondKernel t| := abs_sub _ _
    _ ≤ C / log x + C / log x := by
      rw [abs_div, abs_of_pos hlog]
      exact add_le_add (div_le_div_of_nonneg_right (hbound x hx1.le) hlog.le)
        (by simpa only [Real.norm_eq_abs] using htail)
    _ = (C + C) / log x := (add_div _ _ _).symm

/-- Mertens' second theorem with an `O(1 / log x)` error for real cutoffs. -/
theorem mertensSecond_eventually :
    ∃ C > 0, ∀ᶠ x : ℝ in atTop,
      |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤
        C / log x := by
  obtain ⟨C, hC, hbound⟩ := mertensSecond_bound
  exact ⟨C, hC, (eventually_ge_atTop 2).mono hbound⟩

/-- Natural-number Big-O interface for Mertens' second theorem. -/
theorem mertensSecond_isBigO :
    (fun n : ℕ => primeReciprocalSum n -
      (log (log (n : ℝ)) + mertensSecondConstant)) =O[atTop]
      fun n => 1 / log (n : ℝ) := by
  obtain ⟨D, _hD, hD_bound⟩ := mertensSecond_eventually
  have hreal :
      (fun x : ℝ => primeReciprocalSum ⌊x⌋₊ -
        (log (log x) + mertensSecondConstant)) =O[atTop]
        fun x : ℝ => 1 / log x := by
    apply Asymptotics.IsBigO.of_bound D
    filter_upwards [hD_bound, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hlog : 0 < log x := Real.log_pos hx1
    simpa [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hlog),
      div_eq_mul_inv, abs_of_pos hlog] using hx
  simpa [Nat.floor_natCast] using hreal.natCast_atTop

/-- Natural-number form of Mertens' second theorem, uniform from `n = 2`. -/
theorem mertensSecond_nat :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      |primeReciprocalSum n - (log (log n) + mertensSecondConstant)| ≤
        C / log n := by
  obtain ⟨C, hC, hbound⟩ := mertensSecond_bound
  refine ⟨C, hC, fun n hn => ?_⟩
  simpa only [Nat.floor_natCast] using hbound (n : ℝ) (by exact_mod_cast hn)

end AnalyticNumberTheory.Mertens
