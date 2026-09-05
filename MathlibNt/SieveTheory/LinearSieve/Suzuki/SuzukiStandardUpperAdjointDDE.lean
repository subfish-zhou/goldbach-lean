/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiStandardUpperAdjoint
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

/-!
# The differential--delay equation for Suzuki's standard upper adjoint

This module proves the equation from the defining Laplace integral.  In
particular, the differential--delay equation is not used as an assumption.
-/

namespace MathlibNt.SieveTheory

open Filter Topology MeasureTheory Set

noncomputable section

/-- The elementary first exponential moment is integrable on the positive
half-line. -/
private theorem integrableOn_mul_exp_neg {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-(s * x))) (Ioi 0) := by
  have hgamma : IntegrableOn (fun u : ℝ => Real.exp (-u) * u) (Ioi 0) := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using
      (Real.GammaIntegral_convergent (s := (2 : ℝ)) (by norm_num))
  have hscaled : IntegrableOn (fun x : ℝ => Real.exp (-(s * x)) * (s * x)) (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => Real.exp (-u) * u) 0 hs).mpr (by simpa using hgamma)
  have h := hscaled.const_mul s⁻¹
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  field_simp [hs.ne']

/-- A first exponential moment remains integrable after inserting Suzuki's
nonnegative `Ein` weight. -/
theorem integrableOn_standardUpperAdjoint_moment {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-s * x - suzukiEin x)) (Ioi 0) := by
  apply MeasureTheory.Integrable.mono (integrableOn_mul_exp_neg hs)
  · apply AEStronglyMeasurable.restrict
    have hc : Continuous (fun x : ℝ => x * Real.exp (-s * x - suzukiEin x)) :=
      continuous_id.mul (Real.continuous_exp.comp
        ((continuous_const.neg.mul continuous_id).sub continuous_suzukiEin))
    exact hc.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change |x * Real.exp (-s * x - suzukiEin x)| ≤ |x * Real.exp (-(s * x))|
    rw [abs_mul, abs_mul, abs_of_pos hx, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hx.le
    exact (by
      have hEin := suzukiEin_nonneg (le_of_lt hx)
      linarith)

/-- Differentiation under the defining improper integral, proved by a local
integrable majorant. -/
theorem hasDerivAt_suzukiStandardUpperAdjoint_integral {s : ℝ} (hs : 0 < s) :
    HasDerivAt suzukiStandardUpperAdjoint
      (∫ x : ℝ in Ioi 0, -x * Real.exp (-s * x - suzukiEin x)) s := by
  let F : ℝ → ℝ → ℝ := fun u x => Real.exp (-u * x - suzukiEin x)
  let F' : ℝ → ℝ → ℝ := fun u x => -x * Real.exp (-u * x - suzukiEin x)
  let bound : ℝ → ℝ := fun x => x * Real.exp (-(s / 2) * x)
  have hs2 : 0 < s / 2 := by positivity
  have hbound : IntegrableOn bound (Ioi 0) := by
    dsimp only [bound]
    convert integrableOn_mul_exp_neg hs2 using 1
    ext x
    congr 2
    ring
  have hnhds : Ici (s / 2) ∈ 𝓝 s := by
    exact mem_of_superset (Ioi_mem_nhds (by linarith : s / 2 < s)) Ioi_subset_Ici_self
  have hmeas : ∀ᶠ u in 𝓝 s,
      AEStronglyMeasurable (F u) (volume.restrict (Ioi 0)) := by
    filter_upwards with u
    dsimp only [F]
    apply AEStronglyMeasurable.restrict
    have hc : Continuous (fun x : ℝ => Real.exp (-u * x - suzukiEin x)) :=
      Real.continuous_exp.comp
        ((continuous_const.neg.mul continuous_id).sub continuous_suzukiEin)
    exact hc.aestronglyMeasurable
  have hint : Integrable (F s) (volume.restrict (Ioi 0)) := by
    exact integrableOn_standardUpperAdjoint_integrand hs
  have hF'meas : AEStronglyMeasurable (F' s) (volume.restrict (Ioi 0)) := by
    dsimp only [F']
    apply AEStronglyMeasurable.restrict
    have hc : Continuous (fun x : ℝ => -x * Real.exp (-s * x - suzukiEin x)) :=
      continuous_neg.mul (Real.continuous_exp.comp
        ((continuous_const.neg.mul continuous_id).sub continuous_suzukiEin))
    exact hc.aestronglyMeasurable
  have hderiv : ∀ᵐ x ∂volume.restrict (Ioi 0), ∀ u ∈ Ici (s / 2),
      HasDerivAt (F · x) (F' u x) u := by
    filter_upwards with x
    intro u hu
    dsimp only [F, F']
    have hd := (((hasDerivAt_id u).mul_const x).neg.sub_const (suzukiEin x)).exp
    have hd' : HasDerivAt (fun v : ℝ => Real.exp (-v * x - suzukiEin x))
        (Real.exp (-u * x - suzukiEin x) * (-x)) u := by
      simpa only [Pi.neg_apply, id_eq, one_mul, neg_mul] using hd
    exact hd'.congr_deriv (by ring)
  have hmajor : ∀ᵐ x ∂volume.restrict (Ioi 0), ∀ u ∈ Ici (s / 2),
      ‖F' u x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro u hu
    change |-x * Real.exp (-u * x - suzukiEin x)| ≤
      x * Real.exp (-(s / 2) * x)
    rw [abs_mul, abs_neg, abs_of_pos hx, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hx.le
    have hEin := suzukiEin_nonneg (le_of_lt hx)
    calc
      -u * x - suzukiEin x ≤ -u * x := by linarith
      _ ≤ -(s / 2) * x := mul_le_mul_of_nonneg_right (neg_le_neg hu) hx.le
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (F := F) (F' := F') (bound := bound) hnhds hmeas hint hF'meas hmajor hbound hderiv).2
  change HasDerivAt (fun u : ℝ =>
    ∫ x : ℝ in Ioi 0, Real.exp (-u * x - suzukiEin x))
      (∫ x : ℝ in Ioi 0, -x * Real.exp (-s * x - suzukiEin x)) s
  simpa only [F, F'] using h

/-- The exact derivative before identifying the first moment with a delayed
value. -/
theorem hasDerivAt_suzukiStandardUpperAdjoint_moment {s : ℝ} (hs : 0 < s) :
    HasDerivAt suzukiStandardUpperAdjoint
      (-(∫ x : ℝ in Ioi 0, x * Real.exp (-s * x - suzukiEin x))) s := by
  convert hasDerivAt_suzukiStandardUpperAdjoint_integral hs using 1
  rw [← MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  ring

/-- The finite-interval integration-by-parts identity producing the delay. -/
theorem hasDerivAt_mul_standardUpperAdjoint_integrand (s x : ℝ) :
    HasDerivAt (fun y : ℝ => y * Real.exp (-s * y - suzukiEin y))
      (Real.exp (-(s + 1) * x - suzukiEin x) -
        s * (x * Real.exp (-s * x - suzukiEin x))) x := by
  have hEin := hasDerivAt_suzukiEin (x := x)
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-s * y - suzukiEin y))
      (Real.exp (-s * x - suzukiEin x) * (-s - suzukiEinKernel x)) x := by
    simpa using ((((hasDerivAt_const x s).mul (hasDerivAt_id x)).neg.sub hEin).exp)
  have hprod := (hasDerivAt_id x).mul hexp
  apply hprod.congr_deriv
  change 1 * Real.exp (-s * x - suzukiEin x) +
      x * (Real.exp (-s * x - suzukiEin x) * (-s - suzukiEinKernel x)) = _
  rw [show 1 * Real.exp (-s * x - suzukiEin x) +
      x * (Real.exp (-s * x - suzukiEin x) * (-s - suzukiEinKernel x)) =
      -s * (x * Real.exp (-s * x - suzukiEin x)) +
        Real.exp (-s * x - suzukiEin x) * (1 - x * suzukiEinKernel x) by ring,
    mul_suzukiEinKernel_all]
  rw [show Real.exp (-s * x - suzukiEin x) * (1 - (1 - Real.exp (-x))) =
      Real.exp (-s * x - suzukiEin x) * Real.exp (-x) by ring,
    ← Real.exp_add]
  have hexponents : -s * x - suzukiEin x + -x = -(s + 1) * x - suzukiEin x := by ring
  rw [hexponents]
  ring

/-- The `x`-moment of the defining kernel is exactly the shifted adjoint divided
by the Laplace parameter. -/
theorem standardUpperAdjoint_moment_identity {s : ℝ} (hs : 0 < s) :
    s * (∫ x : ℝ in Ioi 0, x * Real.exp (-s * x - suzukiEin x)) =
      suzukiStandardUpperAdjoint (s + 1) := by
  let m : ℝ → ℝ := fun x => x * Real.exp (-s * x - suzukiEin x)
  let q : ℝ → ℝ := fun x => Real.exp (-(s + 1) * x - suzukiEin x)
  have hmint : IntegrableOn m (Ioi 0) := by
    simpa only [m] using integrableOn_standardUpperAdjoint_moment hs
  have hqint : IntegrableOn q (Ioi 0) := by
    have hs1 : 0 < s + 1 := by linarith
    simpa only [q] using integrableOn_standardUpperAdjoint_integrand hs1
  have hfinite (R : ℝ) (hR : 0 ≤ R) :
      s * (∫ x in Ioc (0 : ℝ) R, m x) =
        (∫ x in Ioc (0 : ℝ) R, q x) -
          R * Real.exp (-s * R - suzukiEin R) := by
    have hderiv (x : ℝ) : HasDerivAt (fun y : ℝ =>
        y * Real.exp (-s * y - suzukiEin y)) (q x - s * m x) x := by
      simpa only [q, m] using hasDerivAt_mul_standardUpperAdjoint_integrand s x
    have hcontq : Continuous q := by
      dsimp only [q]
      exact Real.continuous_exp.comp
        ((continuous_const.neg.mul continuous_id).sub continuous_suzukiEin)
    have hcontm : Continuous m := by
      dsimp only [m]
      exact continuous_id.mul (Real.continuous_exp.comp
        ((continuous_const.neg.mul continuous_id).sub continuous_suzukiEin))
    have hftc : (∫ x in (0 : ℝ)..R, (q x - s * m x)) =
        R * Real.exp (-s * R - suzukiEin R) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)]
      · simp [suzukiEin]
      · exact (hcontq.sub (continuous_const.mul hcontm)).intervalIntegrable 0 R
    rw [intervalIntegral.integral_sub (hcontq.intervalIntegrable 0 R)
        ((hcontm.const_mul s).intervalIntegrable 0 R),
      intervalIntegral.integral_const_mul] at hftc
    rw [← intervalIntegral.integral_of_le hR, ← intervalIntegral.integral_of_le hR]
    linarith
  have hunion : (⋃ n : ℕ, Ioc (0 : ℝ) (n : ℝ)) = Ioi 0 := by
    ext x
    constructor
    · simp only [mem_iUnion, mem_Ioc, mem_Ioi]
      rintro ⟨n, hx, _⟩
      exact hx
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact mem_iUnion.mpr ⟨n, hx, hn.le⟩
  have hmono : Monotone (fun n : ℕ => Ioc (0 : ℝ) (n : ℝ)) := by
    intro a b hab x hx
    exact ⟨hx.1, hx.2.trans (by exact_mod_cast hab)⟩
  have hm_lim : Tendsto (fun n : ℕ => ∫ x in Ioc (0 : ℝ) (n : ℝ), m x)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), m x)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone
      (μ := volume) (f := m) (s := fun n : ℕ => Ioc (0 : ℝ) (n : ℝ))
      (fun _ => measurableSet_Ioc) hmono (by simpa only [hunion] using hmint)
    simpa only [hunion] using h
  have hq_lim : Tendsto (fun n : ℕ => ∫ x in Ioc (0 : ℝ) (n : ℝ), q x)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), q x)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone
      (μ := volume) (f := q) (s := fun n : ℕ => Ioc (0 : ℝ) (n : ℝ))
      (fun _ => measurableSet_Ioc) hmono (by simpa only [hunion] using hqint)
    simpa only [hunion] using h
  have hexp_lim : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(s * (n : ℝ))))
      atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hs)
    have h' := h.const_mul s⁻¹
    convert h' using 1
    · funext n
      simp only [Function.comp_apply, pow_one]
      field_simp [hs.ne']
    · simp
  have hboundary : Tendsto
      (fun n : ℕ => (n : ℝ) * Real.exp (-s * (n : ℝ) - suzukiEin (n : ℝ))) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      positivity
    · intro n
      have hEin : 0 ≤ suzukiEin (n : ℝ) := suzukiEin_nonneg (Nat.cast_nonneg n)
      have hle : -s * (n : ℝ) - suzukiEin (n : ℝ) ≤ -(s * (n : ℝ)) := by
        linarith
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (Nat.cast_nonneg n)
    · simpa only [neg_mul] using hexp_lim
  have hl := hm_lim.const_mul s
  have hr := hq_lim.sub hboundary
  change s * (∫ x in Ioi (0 : ℝ), m x) = ∫ x in Ioi (0 : ℝ), q x
  apply tendsto_nhds_unique hl
  have hr' := hr.congr' (by
    filter_upwards with n
    exact (hfinite n (Nat.cast_nonneg n)).symm)
  simpa only [sub_zero] using hr'

/-- Suzuki's standard upper adjoint satisfies its adjoint differential--delay
equation on the positive half-line. -/
theorem suzukiStandardUpperAdjoint_hasDerivAt_dde {s : ℝ} (hs : 0 < s) :
    HasDerivAt suzukiStandardUpperAdjoint
      (-suzukiStandardUpperAdjoint (s + 1) / s) s := by
  have h := hasDerivAt_suzukiStandardUpperAdjoint_moment hs
  apply h.congr_deriv
  have hm := standardUpperAdjoint_moment_identity hs
  rw [neg_div]
  congr 1
  exact (eq_div_iff hs.ne').2 (by simpa [mul_comm] using hm)


end

end MathlibNt.SieveTheory
