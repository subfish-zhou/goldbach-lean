import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Exact logarithmic moments for the true equation-(21) Mellin tail

This file proves the positive-ray moments and their finite binomial sum.
It does not assume or prove a logarithmic-derivative bound. Integrability is
established by Gamma convergence and change of variables, not totalization.
-/

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators Topology
namespace AnalyticNumberTheory.LargeSieve

/-- Gamma moment used to prove the true Mellin tail integrable before evaluating it. -/
theorem chen1973Lemma6_eq21_expMoment_integrable (N j : ℕ) (hN : 0 < N) :
    IntegrableOn (fun w : ℝ => w ^ j * Real.exp (-((N : ℝ) * w))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (j : ℝ)) (p := 1) (b := (N : ℝ))
    (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    (by norm_num) (by exact_mod_cast hN)
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using h

theorem chen1973Lemma6_eq21_expMoment_integral (N j : ℕ) (hN : 0 < N) :
    (∫ w : ℝ in Ioi 0, w ^ j * Real.exp (-((N : ℝ) * w))) =
      (Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (j : ℝ) + 1) (r := (N : ℝ)) (by positivity) (by exact_mod_cast hN)
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by simp, Real.rpow_natCast] at h
  simpa [one_div, inv_pow, div_eq_mul_inv, mul_comm] using h

private theorem eq21_exp_tail_identity (N j : ℕ) (w : ℝ) :
    Real.exp w * (Real.log (Real.exp w) ^ j / Real.exp w ^ (N + 1)) =
      w ^ j * Real.exp (-((N : ℝ) * w)) := by
  rw [Real.log_exp]
  have hratio : Real.exp w / Real.exp w ^ (N + 1) =
      Real.exp (-((N : ℝ) * w)) := by
    rw [pow_succ, mul_comm (Real.exp w ^ N), div_mul_eq_div_div,
      div_self (Real.exp_ne_zero w), one_div, ← Real.exp_nat_mul, ← Real.exp_neg]
  calc
    _ = w ^ j * (Real.exp w / Real.exp w ^ (N + 1)) := by ring
    _ = _ := by rw [hratio]

/-- Logarithmic tail moment on the unit ray. -/
theorem chen1973Lemma6_eq21_logTail_integrable (N j : ℕ) (hN : 0 < N) :
    IntegrableOn (fun v : ℝ => Real.log v ^ j / v ^ (N + 1)) (Ioi 1) := by
  have h := (integrableOn_comp_exp_Ioi
    (fun v : ℝ => Real.log v ^ j / v ^ (N + 1)) 0)
  simp only [Real.exp_zero] at h
  apply h.mp
  simpa only [smul_eq_mul, eq21_exp_tail_identity] using
    chen1973Lemma6_eq21_expMoment_integrable N j hN

theorem chen1973Lemma6_eq21_logTail_integral (N j : ℕ) (hN : 0 < N) :
    (∫ v : ℝ in Ioi 1, Real.log v ^ j / v ^ (N + 1)) =
      (Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1) := by
  have h := integral_comp_exp_Ioi
    (fun v : ℝ => Real.log v ^ j / v ^ (N + 1)) 0
  simp only [Real.exp_zero, smul_eq_mul, eq21_exp_tail_identity] at h
  rw [← h]
  exact chen1973Lemma6_eq21_expMoment_integral N j hN

private theorem eq21_scaled_tail_identity (N j : ℕ) {a v : ℝ}
    (ha : a ≠ 0) (hv : v ≠ 0) :
    a ^ N / (a * v) ^ (N + 1) * Real.log (a * v / a) ^ j =
      a⁻¹ * (Real.log v ^ j / v ^ (N + 1)) := by
  rw [mul_div_cancel_left₀ v ha, mul_pow, pow_succ a N]
  field_simp

/-- Scale cancellation in the true high-tail moment, including integrability. -/
theorem chen1973Lemma6_eq21_scaledLogTail_integrable
    {a : ℝ} (ha : 0 < a) (N j : ℕ) (hN : 0 < N) :
    IntegrableOn (fun t : ℝ =>
      a ^ N / t ^ (N + 1) * Real.log (t / a) ^ j) (Ioi a) := by
  let f : ℝ → ℝ := fun t => a ^ N / t ^ (N + 1) * Real.log (t / a) ^ j
  have h := integrableOn_Ioi_comp_mul_left_iff f 1 ha
  rw [mul_one] at h
  apply h.mp
  have hbase : IntegrableOn (fun v : ℝ => a⁻¹ *
      (Real.log v ^ j / v ^ (N + 1))) (Ioi 1) :=
    (chen1973Lemma6_eq21_logTail_integrable N j hN).const_mul a⁻¹
  refine hbase.congr_fun (fun v hv => ?_) measurableSet_Ioi
  exact (eq21_scaled_tail_identity N j ha.ne'
    (ne_of_gt (lt_trans zero_lt_one hv))).symm

theorem chen1973Lemma6_eq21_scaledLogTail_integral
    {a : ℝ} (ha : 0 < a) (N j : ℕ) (hN : 0 < N) :
    (∫ t : ℝ in Ioi a,
      a ^ N / t ^ (N + 1) * Real.log (t / a) ^ j) =
      (Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1) := by
  let f : ℝ → ℝ := fun t => a ^ N / t ^ (N + 1) * Real.log (t / a) ^ j
  have hchange := integral_comp_mul_left_Ioi' f 1 ha
  rw [mul_one] at hchange
  change (∫ t in Ioi a, f t) = _
  rw [← hchange]
  have heq : (∫ v in Ioi (1 : ℝ), f (a * v)) =
      ∫ v in Ioi (1 : ℝ), a⁻¹ * (Real.log v ^ j / v ^ (N + 1)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    exact eq21_scaled_tail_identity N j ha.ne' (ne_of_gt (lt_trans zero_lt_one hv))
  rw [heq, integral_const_mul, chen1973Lemma6_eq21_logTail_integral N j hN]
  simp [smul_eq_mul, ha.ne']

private theorem eq21_shiftedLogTail_expansion (a D : ℝ) (N r : ℕ) :
    (fun t : ℝ => a ^ N / t ^ (N + 1) * (D + Real.log (t / a)) ^ r) =
      (fun t : ℝ => ∑ j ∈ Finset.range (r + 1),
        ((Nat.choose r j : ℝ) * D ^ (r - j)) *
          (a ^ N / t ^ (N + 1) * Real.log (t / a) ^ j)) := by
  funext t
  rw [add_comm D, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Arbitrary polynomial logarithmic growth remains integrable in the true tail. -/
theorem chen1973Lemma6_eq21_shiftedLogTail_integrable
    {a : ℝ} (ha : 0 < a) (D : ℝ) (N r : ℕ) (hN : 0 < N) :
    IntegrableOn (fun t : ℝ =>
      a ^ N / t ^ (N + 1) * (D + Real.log (t / a)) ^ r) (Ioi a) := by
  rw [eq21_shiftedLogTail_expansion]
  exact integrable_finsetSum _ (fun j _ =>
    (chen1973Lemma6_eq21_scaledLogTail_integrable ha N j hN).const_mul _)

/-- Exact full high-tail budget, with the scale cancelling and no radial loss. -/
theorem chen1973Lemma6_eq21_shiftedLogTail_integral
    {a : ℝ} (ha : 0 < a) (D : ℝ) (N r : ℕ) (hN : 0 < N) :
    (∫ t : ℝ in Ioi a,
      a ^ N / t ^ (N + 1) * (D + Real.log (t / a)) ^ r) =
      ∑ j ∈ Finset.range (r + 1),
        (Nat.choose r j : ℝ) * D ^ (r - j) *
          ((Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1)) := by
  rw [eq21_shiftedLogTail_expansion]
  rw [integral_finsetSum _ (fun j _ =>
    (chen1973Lemma6_eq21_scaledLogTail_integrable ha N j hN).const_mul _)]
  simp_rw [integral_const_mul, chen1973Lemma6_eq21_scaledLogTail_integral ha N _ hN]

end AnalyticNumberTheory.LargeSieve