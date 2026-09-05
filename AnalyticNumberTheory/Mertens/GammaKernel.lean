import AnalyticNumberTheory.Mertens.Abelian

/-!
# Scaling the Euler--Mascheroni Gamma kernel

This file records the positive-dilation form of the logarithmic Gamma kernel
needed in Abelian finite-part arguments.
-/

namespace AnalyticNumberTheory.Mertens

open Filter Topology Real Set MeasureTheory Asymptotics

/-- The logarithmic Gamma kernel is Bochner integrable on the positive half-line. -/
theorem integrableOn_complex_log_mul_exp_neg :
    IntegrableOn
      (fun t : ℝ => (Real.log t : ℂ) * (Real.exp (-t) : ℂ)) (Ioi 0) := by
  have hconv :=
    (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ)
      ((Continuous.continuousOn
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg))).locallyIntegrableOn
          measurableSet_Ioi)
      (by
        rw [← isBigO_norm_left]
        simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), neg_one_mul] using
          (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-(1 + 1))).isBigO)
      (lt_add_one (1 : ℝ))
      (by
        simp_rw [neg_zero, rpow_zero]
        refine isBigO_const_of_tendsto
          (?_ : Tendsto _ _ (𝓝 (1 : ℂ))) one_ne_zero
        rw [(by simp : (1 : ℂ) = Real.exp (-0))]
        exact
          (Complex.continuous_ofReal.comp
            (Real.continuous_exp.comp continuous_neg)).continuousWithinAt)
      (by norm_num : (0 : ℝ) < (1 : ℂ).re)).1
  simpa [MellinConvergent] using hconv

/-- The positive-dilation exponential kernel has total mass `1 / ε`. -/
theorem complex_scaled_integral_exp_eq_one (ε : ℝ) (hε : 0 < ε) :
    (ε : ℂ) *
        (∫ t : ℝ in Ioi 0, (Real.exp (-(ε * t)) : ℂ)) = 1 := by
  have hscale := integral_comp_mul_left_Ioi'
    (fun u : ℝ => (Real.exp (-u) : ℂ)) 0 hε
  have hscale' :
      ε • (∫ t : ℝ in Ioi 0, (Real.exp (-(ε * t)) : ℂ)) =
        ∫ u : ℝ in Ioi 0, (Real.exp (-u) : ℂ) := by
    simpa only [mul_zero] using hscale
  rw [show (ε : ℂ) * _ = ε •
      (∫ t : ℝ in Ioi 0, (Real.exp (-(ε * t)) : ℂ)) by rfl]
  rw [hscale']
  rw [integral_complex_ofReal]
  norm_cast
  exact integral_exp_neg_Ioi_zero

/-- Integrability of the positive-dilation exponential kernel. -/
theorem integrableOn_complex_exp_neg_mul (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn
      (fun t : ℝ => (Real.exp (-(ε * t)) : ℂ)) (Ioi 0) := by
  have hexpBase : IntegrableOn
      (fun u : ℝ => (Real.exp (-u) : ℂ)) (Ioi 0) := by
    exact (integrableOn_exp_neg_Ioi 0).ofReal
  exact (integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ => (Real.exp (-u) : ℂ)) 0 hε).mpr
      (by simpa only [mul_zero] using hexpBase)

/-- Integrability of the scaled logarithmic Gamma kernel. -/
theorem integrableOn_complex_log_mul_exp_neg_mul (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn
      (fun t : ℝ =>
        (Real.log t : ℂ) * (Real.exp (-(ε * t)) : ℂ)) (Ioi 0) := by
  have hlogScaled : IntegrableOn
      (fun t : ℝ =>
        (Real.log (ε * t) : ℂ) * (Real.exp (-(ε * t)) : ℂ)) (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => (Real.log u : ℂ) * (Real.exp (-u) : ℂ)) 0 hε).mpr
        (by simpa only [mul_zero] using integrableOn_complex_log_mul_exp_neg)
  have hexpScaled : IntegrableOn
      (fun t : ℝ => (Real.exp (-(ε * t)) : ℂ)) (Ioi 0) := by
    exact integrableOn_complex_exp_neg_mul ε hε
  have hsub := hlogScaled.sub
    (hexpScaled.const_mul (Real.log ε : ℂ))
  refine hsub.congr_fun ?_ measurableSet_Ioi
  intro t ht
  change
    (Real.log (ε * t) : ℂ) * (Real.exp (-(ε * t)) : ℂ) -
        (Real.log ε : ℂ) * (Real.exp (-(ε * t)) : ℂ) =
      (Real.log t : ℂ) * (Real.exp (-(ε * t)) : ℂ)
  rw [Real.log_mul hε.ne' (ne_of_gt ht)]
  push_cast
  ring

/-- The logarithmic Gamma kernel after the dilation `u = ε t`.

The statement is complex-valued so that it can directly reuse the Gamma
derivative calculation in `Mertens.Abelian`.
-/
theorem complex_scaled_integral_log_exp_eq_neg_eulerMascheroni
    (ε : ℝ) (hε : 0 < ε) :
    (ε : ℂ) *
          (∫ t : ℝ in Ioi 0,
            (Real.log t : ℂ) * (Real.exp (-(ε * t)) : ℂ)) +
        (Real.log ε : ℂ) =
      (-Real.eulerMascheroniConstant : ℂ) := by
  have hscaled := integral_comp_mul_left_Ioi'
    (fun u : ℝ => (Real.log u : ℂ) * (Real.exp (-u) : ℂ)) 0 hε
  have hscaled' :
      (ε : ℂ) *
          (∫ t : ℝ in Ioi 0,
            (Real.log (ε * t) : ℂ) * (Real.exp (-(ε * t)) : ℂ)) =
        (-Real.eulerMascheroniConstant : ℂ) := by
    rw [show (ε : ℂ) * _ = ε •
        (∫ t : ℝ in Ioi 0,
          (Real.log (ε * t) : ℂ) * (Real.exp (-(ε * t)) : ℂ)) by rfl]
    rw [hscaled]
    simpa using complex_integral_log_exp_eq_neg_eulerMascheroni
  have hlogScaled : IntegrableOn
      (fun t : ℝ =>
        (Real.log (ε * t) : ℂ) * (Real.exp (-(ε * t)) : ℂ)) (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => (Real.log u : ℂ) * (Real.exp (-u) : ℂ)) 0 hε).mpr
        (by simpa using integrableOn_complex_log_mul_exp_neg)
  have hexpBase : IntegrableOn
      (fun u : ℝ => (Real.exp (-u) : ℂ)) (Ioi 0) := by
    exact (integrableOn_exp_neg_Ioi 0).ofReal
  have hexpScaled : IntegrableOn
      (fun t : ℝ => (Real.exp (-(ε * t)) : ℂ)) (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => (Real.exp (-u) : ℂ)) 0 hε).mpr (by simpa using hexpBase)
  have hlogDesired : IntegrableOn
      (fun t : ℝ =>
        (Real.log t : ℂ) * (Real.exp (-(ε * t)) : ℂ)) (Ioi 0) := by
    have hsub := hlogScaled.sub
      (hexpScaled.const_mul (Real.log ε : ℂ))
    refine hsub.congr_fun ?_ measurableSet_Ioi
    intro t ht
    change
      (Real.log (ε * t) : ℂ) * (Real.exp (-(ε * t)) : ℂ) -
          (Real.log ε : ℂ) * (Real.exp (-(ε * t)) : ℂ) =
        (Real.log t : ℂ) * (Real.exp (-(ε * t)) : ℂ)
    rw [Real.log_mul hε.ne' (ne_of_gt ht)]
    push_cast
    ring
  have hsplit :
      (∫ t : ℝ in Ioi 0,
          (Real.log (ε * t) : ℂ) * (Real.exp (-(ε * t)) : ℂ)) =
        (Real.log ε : ℂ) *
            (∫ t : ℝ in Ioi 0, (Real.exp (-(ε * t)) : ℂ)) +
          (∫ t : ℝ in Ioi 0,
            (Real.log t : ℂ) * (Real.exp (-(ε * t)) : ℂ)) := by
    rw [← integral_const_mul]
    rw [← integral_add (hexpScaled.const_mul (Real.log ε : ℂ)) hlogDesired]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change
      (Real.log (ε * t) : ℂ) * (Real.exp (-(ε * t)) : ℂ) =
        (Real.log ε : ℂ) * (Real.exp (-(ε * t)) : ℂ) +
          (Real.log t : ℂ) * (Real.exp (-(ε * t)) : ℂ)
    rw [Real.log_mul hε.ne' (ne_of_gt ht)]
    push_cast
    ring
  have hexpIntegral :
      (ε : ℂ) * (∫ t : ℝ in Ioi 0,
        (Real.exp (-(ε * t)) : ℂ)) = 1 := by
    have hscale := integral_comp_mul_left_Ioi'
      (fun u : ℝ => (Real.exp (-u) : ℂ)) 0 hε
    have hscale' :
        ε • (∫ t : ℝ in Ioi 0, (Real.exp (-(ε * t)) : ℂ)) =
          ∫ u : ℝ in Ioi 0, (Real.exp (-u) : ℂ) := by
      simpa only [mul_zero] using hscale
    rw [show (ε : ℂ) * _ = ε •
        (∫ t : ℝ in Ioi 0, (Real.exp (-(ε * t)) : ℂ)) by rfl]
    rw [hscale']
    rw [integral_complex_ofReal]
    norm_cast
    exact integral_exp_neg_Ioi_zero
  rw [hsplit] at hscaled'
  calc
    (ε : ℂ) *
          (∫ t : ℝ in Ioi 0,
            (Real.log t : ℂ) * (Real.exp (-(ε * t)) : ℂ)) +
        (Real.log ε : ℂ) =
        (ε : ℂ) *
          ((Real.log ε : ℂ) *
              (∫ t : ℝ in Ioi 0, (Real.exp (-(ε * t)) : ℂ)) +
            (∫ t : ℝ in Ioi 0,
              (Real.log t : ℂ) * (Real.exp (-(ε * t)) : ℂ))) := by
          have haux :
              (ε : ℂ) * (Real.log ε : ℂ) *
                  (∫ t : ℝ in Ioi 0, (Real.exp (-(ε * t)) : ℂ)) =
                (Real.log ε : ℂ) := by
            calc
              _ = (Real.log ε : ℂ) *
                    ((ε : ℂ) *
                      (∫ t : ℝ in Ioi 0,
                        (Real.exp (-(ε * t)) : ℂ))) := by ring
              _ = _ := by rw [hexpIntegral, mul_one]
          calc
            _ = (Real.log ε : ℂ) +
                (ε : ℂ) *
                  (∫ t : ℝ in Ioi 0,
                    (Real.log t : ℂ) * (Real.exp (-(ε * t)) : ℂ)) := by ring
            _ = ((ε : ℂ) * (Real.log ε : ℂ) *
                    (∫ t : ℝ in Ioi 0,
                      (Real.exp (-(ε * t)) : ℂ))) +
                  (ε : ℂ) *
                    (∫ t : ℝ in Ioi 0,
                      (Real.log t : ℂ) * (Real.exp (-(ε * t)) : ℂ)) := by
                rw [haux]
            _ = _ := by ring
    _ = (-Real.eulerMascheroniConstant : ℂ) := hscaled'

end AnalyticNumberTheory.Mertens
