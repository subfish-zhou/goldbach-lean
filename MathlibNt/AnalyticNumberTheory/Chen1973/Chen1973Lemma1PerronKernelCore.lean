/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973MellinMoment

/-!
# Chen 1973, Lemma 1: the literal finite Mellin--Perron kernel

This file formalizes the exact finite formula obtained after the Bromwich contour
calculation on pp. 112--113 of Chen's 1973 paper.  It is deliberately independent
of the truncated sine Perron kernel elsewhere in this repository.

For `n = ⌊log x⌋` and `t = (log x)^(11/10) log y`, Chen obtains, for `y ≥ 1`,

`Φ(y) = 1 - exp (-t) * ∑ ν = 0..n, t^ν / ν!`

and identifies this with the normalized integral

`1 / n! * ∫ λ in 0..t, exp (-λ) λ^n dλ`.

The definition below remains honestly named `...Finite`: its identification with
Mathlib's Bochner integral over the full vertical line is proved in the companion
module `Chen1973Lemma1MellinClosure`, which supplies the unconditional
`Chen1973BromwichIdentity`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Interval Topology

namespace AnalyticNumberTheory.LargeSieve

/-- The finite exponential polynomial `∑_{ν=0}^n t^ν / ν!`. -/
def chenExpPartial (n : ℕ) (t : ℝ) : ℝ :=
  ∑ ν ∈ Finset.range (n + 1), t ^ ν / (ν.factorial : ℝ)

@[simp]
theorem chenExpPartial_zero (t : ℝ) : chenExpPartial 0 t = 1 := by
  simp [chenExpPartial]

@[simp]
theorem chenExpPartial_at_zero (n : ℕ) : chenExpPartial n 0 = 1 := by
  induction n with
  | zero => simp [chenExpPartial]
  | succ n ih =>
      rw [chenExpPartial, show n.succ + 1 = (n + 1) + 1 by omega,
        Finset.sum_range_succ]
      rw [← chenExpPartial, ih]
      simp

/-- The source's post-contour normalized Gamma-CDF formula. -/
def chenGammaCDF (n : ℕ) (t : ℝ) : ℝ :=
  1 - Real.exp (-t) * chenExpPartial n t

@[simp]
theorem chenGammaCDF_zero (n : ℕ) : chenGammaCDF n 0 = 0 := by
  simp [chenGammaCDF]

/-- Literal source scale `(log x)^1.1`, written without decimal notation. -/
def chen1973PerronScale (x : ℝ) : ℝ :=
  (Real.log x) ^ ((11 : ℝ) / 10)

/-- Literal integer parameter `[log x]` from Chen 1973. -/
def chen1973PerronOrder (x : ℝ) : ℕ :=
  ⌊Real.log x⌋₊

/--
Chen's Lemma 1 kernel in its exact finite, post-contour form.  The branch at
`y ≤ 1` is the source's strict Perron cutoff; for `y > 1` this is the finite
Gamma-CDF/exponential-sum formula printed on p. 113.
-/
def chen1973PerronKernelFinite (x y : ℝ) : ℝ :=
  if y ≤ 1 then 0 else
    chenGammaCDF (chen1973PerronOrder x)
      (chen1973PerronScale x * Real.log y)

/-- The literal complex integrand on the vertical line `Re ω = 2`.
This is data only; no convergence or contour-shift theorem is asserted here. -/
def chen1973BromwichIntegrand (x y t : ℝ) : ℂ :=
  let ω : ℂ := 2 + t * Complex.I
  let a : ℝ := chen1973PerronScale x
  Complex.cpow (y : ℂ) ω /
    (ω * (1 + ω / a) ^ (chen1973PerronOrder x + 1))

/-- The compactly supported Gamma primitive whose Mellin transform is Chen's
rational Bromwich kernel.  The endpoint value at `r = 1` is zero because
`chenGammaCDF n 0 = 0`. -/
def chen1973GammaDensityPrimitive (x r : ℝ) : ℂ :=
  if r ≤ 0 ∨ 1 ≤ r then 0 else
    (chenGammaCDF (chen1973PerronOrder x)
      (chen1973PerronScale x * Real.log (1 / r)) : ℂ)

/-- The rational function occurring as the Mellin transform of
`chen1973GammaDensityPrimitive`. -/
def chen1973MellinKernel (x : ℝ) (s : ℂ) : ℂ :=
  1 / (s * (1 + s / chen1973PerronScale x) ^ (chen1973PerronOrder x + 1))

/-- Evaluation of the Gamma primitive at the reciprocal variable recovers the
literal finite Perron kernel, including the source cutoff `0 < y ≤ 1`. -/
theorem chen1973GammaDensityPrimitive_one_div {x y : ℝ} (hy : 0 < y) :
    chen1973GammaDensityPrimitive x (1 / y) =
      (chen1973PerronKernelFinite x y : ℂ) := by
  by_cases hy1 : y ≤ 1
  · have hrec : 1 ≤ 1 / y := (le_div_iff₀ hy).2 (by simpa)
    rw [chen1973GammaDensityPrimitive, if_pos (Or.inr hrec),
      chen1973PerronKernelFinite, if_pos hy1]
    norm_num
  · have hy1' : 1 < y := lt_of_not_ge hy1
    have hrecpos : 0 < 1 / y := one_div_pos.mpr hy
    have hreclt : 1 / y < 1 := (div_lt_one₀ hy).2 hy1'
    have hcond : ¬(1 / y ≤ 0 ∨ 1 ≤ 1 / y) := by
      push_neg
      exact ⟨hrecpos, hreclt⟩
    have hlog : Real.log (1 / (1 / y)) = Real.log y := by
      congr 1
      field_simp
    rw [chen1973GammaDensityPrimitive, if_neg hcond,
      chen1973PerronKernelFinite, if_neg hy1, hlog]

/-- The rational Mellin kernel is integrable on Chen's vertical line. -/
theorem verticalIntegrable_chen1973MellinKernel {x : ℝ} (hx : 1 < x) :
    Complex.VerticalIntegrable (chen1973MellinKernel x) 2 := by
  let A := chen1973PerronScale x
  let n := chen1973PerronOrder x
  have hA : 0 < A := by
    dsimp [A, chen1973PerronScale]
    exact Real.rpow_pos_of_pos (Real.log_pos hx) _
  have hbound : ∀ t : ℝ,
      ‖chen1973MellinKernel x (((2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
        A ^ (n + 1 : ℕ) * (1 + t ^ 2)⁻¹ := by
    intro t
    let ω : ℂ := (((2 : ℝ) : ℂ) + t * Complex.I)
    let η : ℂ := (A + 2 : ℂ) + t * Complex.I
    have hηeq : 1 + ω / A = η / A := by
      apply Complex.ext <;> simp [ω, η, hA.ne', add_comm, add_left_comm, add_assoc,
        div_eq_mul_inv, mul_add, add_mul]
    have hnormω : ‖ω‖ ^ 2 = 4 + t ^ 2 := by
      rw [Complex.sq_norm]
      simp [ω, Complex.normSq_apply, pow_two]
      norm_num
    have hnormη : ‖η‖ ^ 2 = (A + 2)^2 + t ^ 2 := by
      rw [Complex.sq_norm]
      simp [η, Complex.normSq_apply, pow_two]
    have hωge1 : 1 ≤ ‖ω‖ := by
      have hs : 1 ≤ ‖ω‖ ^ 2 := by
        rw [hnormω]
        nlinarith [sq_nonneg t]
      nlinarith [norm_nonneg ω, sq_nonneg (‖ω‖ - 1)]
    have hηgeω : ‖ω‖ ≤ ‖η‖ := by
      have hsq : ‖ω‖ ^ 2 ≤ ‖η‖ ^ 2 := by
        rw [hnormω, hnormη]
        nlinarith [sq_nonneg (A + 2), hA]
      exact (sq_le_sq₀ (norm_nonneg ω) (norm_nonneg η)).mp hsq
    have hηpow : ‖ω‖ ≤ ‖η‖ ^ (n + 1) := by
      calc
        ‖ω‖ ≤ ‖η‖ := hηgeω
        _ ≤ ‖η‖ ^ (n + 1) := by
          have hηge1 : 1 ≤ ‖η‖ := hωge1.trans hηgeω
          simpa using pow_le_pow_right₀ hηge1 (show 1 ≤ n + 1 by omega)
    have hnorm :
        ‖1 / (ω * (1 + ω / A) ^ (n + 1))‖ =
          A ^ (n + 1 : ℕ) / (‖ω‖ * ‖η‖ ^ (n + 1)) := by
      rw [norm_div, norm_mul, norm_pow, hηeq, norm_div, div_pow]
      simp [hA.ne', abs_of_pos hA, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    change ‖1 / (ω * (1 + ω / A) ^ (n + 1))‖ ≤ _
    rw [hnorm]
    calc
      A ^ (n + 1 : ℕ) / (‖ω‖ * ‖η‖ ^ (n + 1)) ≤
          A ^ (n + 1 : ℕ) / (‖ω‖ * ‖ω‖) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            gcongr
      _ = A ^ (n + 1 : ℕ) / (4 + t ^ 2) := by
            rw [← pow_two, hnormω]
      _ ≤ A ^ (n + 1 : ℕ) * (1 + t ^ 2)⁻¹ := by
            have hi : (4 + t ^ 2)⁻¹ ≤ (1 + t ^ 2)⁻¹ :=
              inv_anti₀ (by nlinarith [sq_nonneg t]) (by nlinarith [sq_nonneg t])
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left hi (pow_nonneg hA.le _)
  rw [Complex.VerticalIntegrable]
  have hdom : Integrable (fun t : ℝ => A ^ (n + 1 : ℕ) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  apply Integrable.mono' hdom
  · unfold chen1973MellinKernel
    measurability
  · filter_upwards with t
    exact hbound t

/-- Parameterizing the inverse Mellin transform on `re s = 2` gives Chen's
real-line Bromwich integral. -/
theorem mellinInv_chen1973MellinKernel_eq_bromwich {x y : ℝ} (hy : 0 < y) :
    mellinInv 2 (chen1973MellinKernel x) (1 / y) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, chen1973BromwichIntegrand x y t) := by
  rw [mellinInv]
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      ((((1 / y : ℝ) : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * Complex.I))) *
        chen1973MellinKernel x (((2 : ℝ) : ℂ) + t * Complex.I))) = _
  congr 2
  ext t
  unfold chen1973MellinKernel chen1973BromwichIntegrand
  let w : ℂ := (((2 : ℝ) : ℂ) + t * Complex.I)
  have hpow : (((1 / y : ℝ) : ℂ) ^ (-w)) = Complex.cpow (y : ℂ) w := by
    have h1 : (((1 / y : ℝ) : ℂ) ^ (-w)) = (((y : ℂ)⁻¹) ^ (-w)) := by
      congr 1
      simp [one_div]
    rw [h1, Complex.inv_cpow_ofReal_nonneg hy.le, Complex.cpow_neg]
    simp
  rw [show -(((2 : ℝ) : ℂ) + t * Complex.I) = -w by rfl, hpow]
  simp [w, div_eq_mul_inv]

/--
Mellin inversion specialized to Chen's Gamma primitive, with its three analytic
premises exposed.  `Chen1973Lemma1MellinClosure` discharges these premises and
publishes the unconditional `Chen1973BromwichIdentity`.
-/
theorem chen1973BromwichIdentity_of_mellin (x : ℝ) (hx : 1 < x)
    (hMellin : ∀ s : ℂ, s.re = 2 →
      mellin (chen1973GammaDensityPrimitive x) s = chen1973MellinKernel x s)
    (hconv : MellinConvergent (chen1973GammaDensityPrimitive x) 2)
    (hcont : ∀ r : ℝ, 0 < r → ContinuousAt (chen1973GammaDensityPrimitive x) r) :
    ∀ y : ℝ, 0 < y →
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ, chen1973BromwichIntegrand x y t) =
        (chen1973PerronKernelFinite x y : ℂ) := by
  intro y hy
  have hv : Complex.VerticalIntegrable
      (mellin (chen1973GammaDensityPrimitive x)) 2 := by
    rw [Complex.VerticalIntegrable]
    apply (verticalIntegrable_chen1973MellinKernel hx).congr
    filter_upwards with t
    exact (hMellin _ (by simp)).symm
  have hinv := mellinInv_mellin_eq 2 (chen1973GammaDensityPrimitive x)
    (one_div_pos.mpr hy) hconv hv (hcont _ (one_div_pos.mpr hy))
  have hreplace : mellinInv 2 (mellin (chen1973GammaDensityPrimitive x)) (1 / y) =
      mellinInv 2 (chen1973MellinKernel x) (1 / y) := by
    unfold mellinInv
    congr 2
    ext t
    rw [hMellin]
    simp
  rw [hreplace, mellinInv_chen1973MellinKernel_eq_bromwich hy] at hinv
  rw [hinv, chen1973GammaDensityPrimitive_one_div hy]

@[simp]
theorem chen1973PerronKernelFinite_of_le_one {x y : ℝ} (hy : y ≤ 1) :
    chen1973PerronKernelFinite x y = 0 := by
  simp [chen1973PerronKernelFinite, hy]

@[simp]
theorem chen1973PerronKernelFinite_zero (x : ℝ) :
    chen1973PerronKernelFinite x 0 = 0 := by
  exact chen1973PerronKernelFinite_of_le_one (by norm_num)

/-- Chen's printed finite exponential-sum identity on the `y > 1` branch. -/
theorem chen1973PerronKernelFinite_of_one_lt {x y : ℝ} (hy : 1 < y) :
    chen1973PerronKernelFinite x y =
      1 - Real.exp (-(chen1973PerronScale x * Real.log y)) *
        ∑ ν ∈ Finset.range (chen1973PerronOrder x + 1),
          (chen1973PerronScale x * Real.log y) ^ ν / (ν.factorial : ℝ) := by
  simp [chen1973PerronKernelFinite, chenGammaCDF, chenExpPartial, not_le_of_gt hy]

/-- The complementary tail is exactly Chen's finite exponential sum. -/
theorem one_sub_chenGammaCDF (n : ℕ) (t : ℝ) :
    1 - chenGammaCDF n t = Real.exp (-t) * chenExpPartial n t := by
  simp [chenGammaCDF]

/-- Recurrence obtained by peeling off the final term of the finite exponential sum. -/
theorem chenGammaCDF_succ (n : ℕ) (t : ℝ) :
    chenGammaCDF (n + 1) t = chenGammaCDF n t -
      Real.exp (-t) * t ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  simp only [chenGammaCDF, chenExpPartial]
  rw [show n + 1 + 1 = (n + 1) + 1 by omega, Finset.sum_range_succ]
  ring

/-- The derivative of the finite Gamma CDF is its normalized Gamma density. -/
theorem hasDerivAt_chenGammaCDF (n : ℕ) (t : ℝ) :
    HasDerivAt (chenGammaCDF n)
      (Real.exp (-t) * t ^ n / (n.factorial : ℝ)) t := by
  induction n with
  | zero =>
      have h := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_sub 1
      have heq : chenGammaCDF 0 =ᶠ[𝓝 t] (fun u => 1 - Real.exp (-u)) :=
        Filter.Eventually.of_forall fun u => by simp [chenGammaCDF]
      exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)
  | succ n ih =>
      let tail : ℝ → ℝ := fun u =>
        Real.exp (-u) * u ^ (n + 1) / ((n + 1).factorial : ℝ)
      have htail0 := (((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).mul
        (hasDerivAt_pow (n + 1) t)).div_const ((n + 1).factorial : ℝ)
      have heqtail : tail =ᶠ[𝓝 t]
          (fun u => Real.exp (-u) * u ^ (n + 1) / ((n + 1).factorial : ℝ)) :=
        Filter.Eventually.of_forall fun _ => rfl
      have htail := htail0.congr_of_eventuallyEq heqtail
      have h := ih.sub htail
      have heq : chenGammaCDF (n + 1) =ᶠ[𝓝 t] chenGammaCDF n - tail :=
        Filter.Eventually.of_forall fun u => chenGammaCDF_succ n u
      refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
      have hpow : n + 1 - 1 = n := by omega
      simp only [Function.comp_apply, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      field_simp
      rw [hpow]
      ring

/-- Chen's finite formula equals the normalized interval Gamma integral exactly. -/
theorem chenGammaCDF_eq_intervalIntegral (n : ℕ) (t : ℝ) :
    chenGammaCDF n t =
      (1 / (n.factorial : ℝ)) *
        ∫ u in (0 : ℝ)..t, Real.exp (-u) * u ^ n := by
  have hint : IntervalIntegrable
      (fun u : ℝ => Real.exp (-u) * u ^ n / (n.factorial : ℝ)) volume 0 t :=
    (((Real.continuous_exp.comp continuous_neg).mul (continuous_pow n)).div_const _).intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (f := chenGammaCDF n)
    (f' := fun u => Real.exp (-u) * u ^ n / (n.factorial : ℝ))
    (fun u _ => hasDerivAt_chenGammaCDF n u) hint
  rw [chenGammaCDF_zero, sub_zero] at hFTC
  rw [← hFTC, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  ring

/-- The finite Gamma CDF is monotone on its source range. -/
theorem chenGammaCDF_monotoneOn (n : ℕ) :
    MonotoneOn (chenGammaCDF n) (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
  · intro u _
    exact (hasDerivAt_chenGammaCDF n u).continuousAt.continuousWithinAt
  · intro u _
    exact (hasDerivAt_chenGammaCDF n u).hasDerivWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hu.le n))
      (Nat.cast_nonneg _)

/-- Every term in Chen's finite exponential polynomial is nonnegative for `t ≥ 0`. -/
theorem chenExpPartial_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ chenExpPartial n t := by
  unfold chenExpPartial
  exact Finset.sum_nonneg fun ν _ =>
    div_nonneg (pow_nonneg ht ν) (Nat.cast_nonneg ν.factorial)

/-- The exponential Taylor lower bound controls the finite polynomial. -/
theorem chenExpPartial_le_exp (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    chenExpPartial n t ≤ Real.exp t := by
  simpa [chenExpPartial] using Real.sum_le_exp_of_nonneg ht (n + 1)

/-- A convenient exponentially decaying majorant for Chen's finite tail. -/
theorem chenExpPartial_le_two_pow_mul_exp_half (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    chenExpPartial n t ≤ (2 : ℝ) ^ n * Real.exp (t / 2) := by
  calc
    chenExpPartial n t = ∑ ν ∈ Finset.range (n + 1),
        (2 : ℝ) ^ ν * ((t / 2) ^ ν / (ν.factorial : ℝ)) := by
      apply Finset.sum_congr rfl
      intro ν _
      rw [← mul_div_assoc, ← mul_pow, show (2 : ℝ) * (t / 2) = t by ring]
    _ ≤ ∑ ν ∈ Finset.range (n + 1),
        (2 : ℝ) ^ n * ((t / 2) ^ ν / (ν.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro ν hν
      have hνn : ν ≤ n := by simpa using (Finset.mem_range.mp hν)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hνn)
        (div_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _))
    _ = (2 : ℝ) ^ n * chenExpPartial n (t / 2) := by
      simp [chenExpPartial, Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ n * Real.exp (t / 2) := by
      gcongr
      exact chenExpPartial_le_exp n (by linarith)

/-- The complementary CDF tail is at most `2^n exp (-t/2)` for `t ≥ 0`. -/
theorem one_sub_chenGammaCDF_le_two_pow_mul_exp_neg_half
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    1 - chenGammaCDF n t ≤ (2 : ℝ) ^ n * Real.exp (-t / 2) := by
  rw [one_sub_chenGammaCDF]
  calc
    Real.exp (-t) * chenExpPartial n t ≤
        Real.exp (-t) * ((2 : ℝ) ^ n * Real.exp (t / 2)) := by
      gcongr
      exact chenExpPartial_le_two_pow_mul_exp_half n ht
    _ = (2 : ℝ) ^ n * (Real.exp (-t) * Real.exp (t / 2)) := by ring
    _ = (2 : ℝ) ^ n * Real.exp (-t / 2) := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- The Gamma-CDF finite formula lies in `[0,1]` on the source range `t ≥ 0`. -/
theorem chenGammaCDF_mem_Icc (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    chenGammaCDF n t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [chenGammaCDF, sub_nonneg]
    calc
      Real.exp (-t) * chenExpPartial n t ≤ Real.exp (-t) * Real.exp t := by
        gcongr
        exact chenExpPartial_le_exp n ht
      _ = 1 := by rw [← Real.exp_add]; simp
  · rw [chenGammaCDF, sub_le_self_iff]
    exact mul_nonneg (Real.exp_pos _).le (chenExpPartial_nonneg n ht)

/-- Exact two-sided tail enclosure furnished by the finite source formula. -/
theorem chenGammaCDF_tail_mem_Icc (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    1 - chenGammaCDF n t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [one_sub_chenGammaCDF]
    exact mul_nonneg (Real.exp_pos _).le (chenExpPartial_nonneg n ht)
  · linarith [(chenGammaCDF_mem_Icc n ht).1]

/-- Source-range positivity of the transformed coordinate. -/
theorem chen1973PerronArgument_nonneg {x y : ℝ} (hx : 1 < x) (hy : 1 ≤ y) :
    0 ≤ chen1973PerronScale x * Real.log y := by
  exact mul_nonneg (Real.rpow_nonneg (Real.log_pos hx).le _)
    (Real.log_nonneg hy)

/-- Consequently the literal finite kernel is between zero and one. -/
theorem chen1973PerronKernelFinite_mem_Icc {x y : ℝ} (hx : 1 < x) (_hy : 0 ≤ y) :
    chen1973PerronKernelFinite x y ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : y ≤ 1
  · simp [chen1973PerronKernelFinite, h]
  · rw [chen1973PerronKernelFinite, if_neg h]
    exact chenGammaCDF_mem_Icc _
      (chen1973PerronArgument_nonneg hx (le_of_lt (lt_of_not_ge h)))

/-- For fixed `x > 1`, Chen's finite kernel is monotone on nonnegative inputs. -/
theorem chen1973PerronKernelFinite_monotoneOn {x : ℝ} (hx : 1 < x) :
    MonotoneOn (chen1973PerronKernelFinite x) (Set.Ici 0) := by
  intro y hy z hz hyz
  by_cases hy1 : y ≤ 1
  · rw [chen1973PerronKernelFinite_of_le_one hy1]
    exact (chen1973PerronKernelFinite_mem_Icc hx hz).1
  · have hz1 : 1 < z := lt_of_lt_of_le (lt_of_not_ge hy1) hyz
    rw [chen1973PerronKernelFinite_of_one_lt (lt_of_not_ge hy1),
      chen1973PerronKernelFinite_of_one_lt hz1]
    apply chenGammaCDF_monotoneOn (chen1973PerronOrder x)
      (chen1973PerronArgument_nonneg hx (le_of_lt (lt_of_not_ge hy1)))
      (chen1973PerronArgument_nonneg hx hz1.le)
    exact mul_le_mul_of_nonneg_left
      (Real.strictMonoOn_log.monotoneOn
        (lt_trans zero_lt_one (lt_of_not_ge hy1)) (lt_trans zero_lt_one hz1) hyz)
      (Real.rpow_nonneg (Real.log_pos hx).le _)

/--
Chen's explicit lower bound in the original numerical range.  The proof is
purely analytic: the finite tail is bounded by `2^n exp (-t/2)`, then
`n = ⌊log x⌋ ≤ log x`, `log 2 < 9/10`, and `t ≥ 2 log x` give the result.
-/
theorem chen1973PerronKernelFinite_lower_bound {x y : ℝ}
    (hx1 : 1 < x) (hx : (10 : ℝ) ^ 7 ≤ Real.log x)
    (hy : Real.exp (2 * (Real.log x) ^ (-(1 : ℝ) / 10)) ≤ y) :
    1 - x ^ (-(1 : ℝ) / 10) ≤ chen1973PerronKernelFinite x y := by
  let L : ℝ := Real.log x
  have hLpos : 0 < L := by dsimp [L]; norm_num at hx ⊢; linarith
  have hxpos : 0 < x := zero_lt_one.trans hx1
  have hypos : 0 < y := (Real.exp_pos _).trans_le hy
  have hlogy : 2 * L ^ (-(1 : ℝ) / 10) ≤ Real.log y := by
    calc
      2 * L ^ (-(1 : ℝ) / 10) =
          Real.log (Real.exp (2 * L ^ (-(1 : ℝ) / 10))) := by rw [Real.log_exp]
      _ ≤ Real.log y := Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hypos hy
  have hscale : chen1973PerronScale x = L ^ ((11 : ℝ) / 10) := rfl
  have hpowcancel : L ^ ((11 : ℝ) / 10) * L ^ (-(1 : ℝ) / 10) = L := by
    rw [← Real.rpow_add hLpos]
    norm_num
  have ht : 2 * L ≤ chen1973PerronScale x * Real.log y := by
    rw [hscale]
    calc
      2 * L = L ^ ((11 : ℝ) / 10) * (2 * L ^ (-(1 : ℝ) / 10)) := by
        calc
          _ = 2 * (L ^ ((11 : ℝ) / 10) * L ^ (-(1 : ℝ) / 10)) :=
            congrArg (fun z : ℝ => 2 * z) hpowcancel.symm
          _ = _ := by ring
      _ ≤ L ^ ((11 : ℝ) / 10) * Real.log y := by gcongr
  have ht0 : 0 ≤ chen1973PerronScale x * Real.log y := by linarith
  have hy1 : 1 < y := (Real.one_lt_exp_iff.mpr
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos hLpos _))).trans_le hy
  rw [chen1973PerronKernelFinite, if_neg (not_le_of_gt hy1)]
  have htail := one_sub_chenGammaCDF_le_two_pow_mul_exp_neg_half
    (chen1973PerronOrder x) ht0
  suffices (2 : ℝ) ^ chen1973PerronOrder x *
      Real.exp (-(chen1973PerronScale x * Real.log y) / 2) ≤
        x ^ (-(1 : ℝ) / 10) by linarith
  have hnL : ((chen1973PerronOrder x : ℕ) : ℝ) ≤ L := Nat.floor_le hLpos.le
  have hlog2 : Real.log 2 ≤ (9 : ℝ) / 10 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hnnonneg : (0 : ℝ) ≤ chen1973PerronOrder x := by positivity
  have hpowexp : (2 : ℝ) ^ chen1973PerronOrder x *
        Real.exp (-(chen1973PerronScale x * Real.log y) / 2) =
      Real.exp (((chen1973PerronOrder x : ℕ) : ℝ) * Real.log 2 -
        (chen1973PerronScale x * Real.log y) / 2) := by
    calc
      _ = Real.exp (Real.log 2) ^ chen1973PerronOrder x *
          Real.exp (-(chen1973PerronScale x * Real.log y) / 2) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp (((chen1973PerronOrder x : ℕ) : ℝ) * Real.log 2) *
          Real.exp (-(chen1973PerronScale x * Real.log y) / 2) := by
            rw [Real.exp_nat_mul]
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [hpowexp, Real.rpow_def_of_pos hxpos]
  apply Real.exp_le_exp.mpr
  have hnlog : ((chen1973PerronOrder x : ℕ) : ℝ) * Real.log 2 ≤
      L * ((9 : ℝ) / 10) := by
    calc
      _ ≤ ((chen1973PerronOrder x : ℕ) : ℝ) * ((9 : ℝ) / 10) := by gcongr
      _ ≤ L * ((9 : ℝ) / 10) := by gcongr
  linarith

end AnalyticNumberTheory.LargeSieve
