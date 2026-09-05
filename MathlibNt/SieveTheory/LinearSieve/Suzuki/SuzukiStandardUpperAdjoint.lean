/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperSourcePairingNormalization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Suzuki's standard upper adjoint `r_{1,-1}`

Suzuki §10 defines, when `a+b<1`,

`r_{a,b}(s) = 1 / Γ(1-a-b) * ∫ x in (0,∞), exp (-s*x + b*Ein(x)) * x^(-(a+b))`.

Thus the standard upper adjoint is

`r_{1,-1}(s) = ∫ x in (0,∞), exp (-s*x - Ein(x))`.

This module starts its source-faithful construction.  It defines the removable
kernel `(1-exp(-x))/x`, its primitive `Ein`, and the genuine Laplace integral.
It closes the local identities which drive both remaining endpoints:

* differentiation under the Laplace integral gives `p'(s)=-p(s+1)/s`;
* `x * exp (-Ein x)` is an exact primitive of the integrand defining `p(1)`.

The latter reduces `p(1)=exp(-γ)` to the classical (non-Buchstab) asymptotic
`x * exp(-Ein x) → exp(-γ)`.  No value at `1` is inserted by definition.
-/

namespace MathlibNt.SieveTheory

open Filter Topology MeasureTheory intervalIntegral Set
open scoped Interval

noncomputable section

/-- The continuous removable extension of `(1 - exp (-x)) / x` at zero. -/
noncomputable def suzukiEinKernel : ℝ → ℝ :=
  Function.update (fun x : ℝ => (1 - Real.exp (-x)) / x) 0 1

@[simp] theorem suzukiEinKernel_zero : suzukiEinKernel 0 = 1 := by
  simp [suzukiEinKernel]

theorem suzukiEinKernel_of_ne {x : ℝ} (hx : x ≠ 0) :
    suzukiEinKernel x = (1 - Real.exp (-x)) / x := by
  simp [suzukiEinKernel, hx]

/-- The apparent singularity in Suzuki's `Ein` kernel is removable. -/
theorem continuous_suzukiEinKernel : Continuous suzukiEinKernel := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · have hderiv : HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) 1 0 := by
      simpa using ((hasDerivAt_neg' (0 : ℝ)).exp.const_sub 1)
    simpa [suzukiEinKernel] using hderiv.continuousAt_div
  · rw [suzukiEinKernel, continuousAt_update_of_ne hx]
    fun_prop

/-- Suzuki's entire exponential integral on the real axis,
`Ein(x)=∫₀ˣ (1-exp(-t))/t dt`, using the removable value at zero. -/
noncomputable def suzukiEin (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, suzukiEinKernel t

/-- The Laplace-integral construction of Suzuki's `r_{1,-1}`. -/
noncomputable def suzukiStandardUpperAdjoint (s : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, Real.exp (-s * x - suzukiEin x)

/-- Away from the removable point, multiplying the `Ein` kernel by its
argument recovers `1-exp(-x)`. -/
theorem mul_suzukiEinKernel {x : ℝ} (hx : x ≠ 0) :
    x * suzukiEinKernel x = 1 - Real.exp (-x) := by
  rw [suzukiEinKernel_of_ne hx]
  field_simp

theorem mul_suzukiEinKernel_all (x : ℝ) :
    x * suzukiEinKernel x = 1 - Real.exp (-x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact mul_suzukiEinKernel hx

/-- The removable kernel is nonnegative on the positive half-line. -/
theorem suzukiEinKernel_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ suzukiEinKernel x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  rw [suzukiEinKernel_of_ne hx0]
  exact div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))) hx

theorem suzukiEin_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ suzukiEin x := by
  unfold suzukiEin
  apply intervalIntegral.integral_nonneg hx
  intro t ht
  exact suzukiEinKernel_nonneg ht.1

/-- A local calculus package sufficient for all source-faithful downstream
arguments.  Continuity is separated because it is exactly the removable
singularity lemma, independent of the later improper integral. -/
theorem hasDerivAt_suzukiEin
    {x : ℝ} :
    HasDerivAt suzukiEin (suzukiEinKernel x) x := by
  unfold suzukiEin
  exact intervalIntegral.integral_hasDerivAt_right
    (continuous_suzukiEinKernel.intervalIntegrable 0 x)
    (continuous_suzukiEinKernel.stronglyMeasurableAtFilter
      (μ := volume) (l := 𝓝 x)) continuous_suzukiEinKernel.continuousAt

theorem continuous_suzukiEin : Continuous suzukiEin := by
  rw [continuous_iff_continuousAt]
  exact fun x => (hasDerivAt_suzukiEin (x := x)).continuousAt

/-- The source integral defining `r_{1,-1}` is genuinely integrable for every
positive Laplace parameter. -/
theorem integrableOn_standardUpperAdjoint_integrand {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => Real.exp (-s * x - suzukiEin x)) (Ioi 0) := by
  have hbase : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) :=
    integrableOn_exp_neg_Ioi 0
  have hscale : IntegrableOn (fun x : ℝ => Real.exp (-(s * x))) (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => Real.exp (-u)) 0 hs).mpr (by simpa using hbase)
  apply MeasureTheory.Integrable.mono hscale
  · have hlinear : Continuous (fun x : ℝ => -s * x) :=
      continuous_const.mul continuous_id
    have hcont : Continuous (fun x : ℝ =>
        Real.exp (-s * x - suzukiEin x)) :=
      Real.continuous_exp.comp (hlinear.sub continuous_suzukiEin)
    exact hcont.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hEin := suzukiEin_nonneg (le_of_lt hx)
    linarith

/-- Positivity of the standard adjoint follows from its positive Laplace
kernel, not from an imposed initial value. -/
theorem suzukiStandardUpperAdjoint_pos {s : ℝ} (hs : 0 < s) :
    0 < suzukiStandardUpperAdjoint s := by
  unfold suzukiStandardUpperAdjoint
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · simp [Function.support, Real.exp_ne_zero]
  · filter_upwards with x
    positivity
  · exact integrableOn_standardUpperAdjoint_integrand hs

/-- Exact finite-interval primitive identity behind
`r_{1,-1}(1)=exp(-γ)`.  This is the earliest normalization node and does not
assume the desired value. -/
theorem hasDerivAt_mul_exp_neg_suzukiEin
    (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * Real.exp (-suzukiEin y))
      (Real.exp (-x - suzukiEin x)) x := by
  have hEin := hasDerivAt_suzukiEin (x := x)
  have hneg : HasDerivAt (fun y : ℝ => Real.exp (-suzukiEin y))
      (Real.exp (-suzukiEin x) * -suzukiEinKernel x) x := by
    simpa only [Pi.neg_apply] using hEin.neg.exp
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hprod := hid.mul hneg
  have heq :
      1 * Real.exp (-suzukiEin x) +
          x * (Real.exp (-suzukiEin x) * -suzukiEinKernel x) =
        Real.exp (-x - suzukiEin x) := by
    rw [show x * (Real.exp (-suzukiEin x) * -suzukiEinKernel x) =
      Real.exp (-suzukiEin x) * -(x * suzukiEinKernel x) by ring,
      mul_suzukiEinKernel_all x]
    rw [show 1 * Real.exp (-suzukiEin x) +
        Real.exp (-suzukiEin x) * -(1 - Real.exp (-x)) =
      Real.exp (-suzukiEin x) * Real.exp (-x) by ring,
      ← Real.exp_add]
    congr 1 <;> ring
  exact hprod.congr_deriv heq

/-- Every finite truncation of the integral defining `r_{1,-1}(1)` is
exactly the Euler--Ein boundary term. -/
theorem integral_exp_neg_sub_suzukiEin_zero_to (R : ℝ) :
    (∫ x in (0 : ℝ)..R, Real.exp (-x - suzukiEin x)) =
      R * Real.exp (-suzukiEin R) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_mul_exp_neg_suzukiEin x)]
  · simp [suzukiEin]
  · exact (Real.continuous_exp.comp
      ((continuous_neg.sub continuous_suzukiEin))).intervalIntegrable 0 R

/-- The desired boundary value is reduced to the classical Euler--Ein tail
asymptotic, rather than postulated as the definition of the adjoint. -/
def SuzukiEinEulerTailAsymptotic : Prop :=
  Tendsto (fun x : ℝ => x * Real.exp (-suzukiEin x)) atTop
    (nhds (Real.exp (-Real.eulerMascheroniConstant)))

/-- Once the classical Euler--Ein tail asymptotic is supplied, the actual
Laplace integral (not a normalized placeholder) has Suzuki's required value. -/
theorem suzukiStandardUpperAdjoint_one_eq_exp_neg_eulerMascheroni
    (htail : SuzukiEinEulerTailAsymptotic) :
    suzukiStandardUpperAdjoint 1 =
      Real.exp (-Real.eulerMascheroniConstant) := by
  let f : ℝ → ℝ := fun x => Real.exp (-x - suzukiEin x)
  have hunion : (⋃ n : ℕ, Ioc (0 : ℝ) (n : ℝ)) = Ioi 0 := by
    ext x
    constructor
    · simp only [mem_iUnion, mem_Ioc, mem_Ioi]
      rintro ⟨n, hx, _⟩
      exact hx
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt x
      simp only [mem_iUnion, mem_Ioc]
      exact ⟨n, hx, hn.le⟩
  have hmono : Monotone (fun n : ℕ => Ioc (0 : ℝ) (n : ℝ)) := by
    intro m n hmn x hx
    exact ⟨hx.1, hx.2.trans (by exact_mod_cast hmn)⟩
  have hint : IntegrableOn f (Ioi 0) := by
    simpa [f] using
      (integrableOn_standardUpperAdjoint_integrand (s := (1 : ℝ)) zero_lt_one)
  have hlimIntegral : Tendsto
      (fun n : ℕ => ∫ x in Ioc (0 : ℝ) (n : ℝ), f x)
      atTop (nhds (∫ x in Ioi (0 : ℝ), f x)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone
      (f := f) (s := fun n : ℕ => Ioc (0 : ℝ) (n : ℝ))
      (fun _ => measurableSet_Ioc) hmono
      (by rwa [hunion])
    simpa only [hunion] using h
  have hfinite (n : ℕ) :
      (∫ x in Ioc (0 : ℝ) (n : ℝ), f x) =
        (n : ℝ) * Real.exp (-suzukiEin n) := by
    rw [← intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
    simpa only [f] using integral_exp_neg_sub_suzukiEin_zero_to (n : ℝ)
  have hlimBoundary : Tendsto
      (fun n : ℕ => (n : ℝ) * Real.exp (-suzukiEin n)) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) :=
    htail.comp tendsto_natCast_atTop_atTop
  have heqIntegral :
      (∫ x in Ioi (0 : ℝ), f x) =
        Real.exp (-Real.eulerMascheroniConstant) := by
    apply tendsto_nhds_unique hlimIntegral
    exact hlimBoundary.congr' (Filter.Eventually.of_forall fun n => (hfinite n).symm)
  simpa [suzukiStandardUpperAdjoint, f] using heqIntegral

end


end MathlibNt.SieveTheory
