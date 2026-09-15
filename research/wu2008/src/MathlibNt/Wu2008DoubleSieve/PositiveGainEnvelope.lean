import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralEnvelope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Wu2008DoubleSieve
open Real Set LiLiuPrereqBuchstab
open scoped Interval

/-- A parameter-dependent majorant, valid for the entire unbounded phi domain. -/
theorem positiveGain_kernel_le {φ t a b c : ℝ} (hφ : 2 ≤ φ)
    (ht : 0 < t) (ha : a ∈ Icc (1 / 10) (1 / 2))
    (hb : b ∈ Icc (1 / 10) (1 / 2)) (hc : c ∈ Icc (1 / 10) (1 / 2))
    (hat : 1 / t ≤ a) (hbt : 1 / t ≤ b) (hct : 1 / t ≤ c) :
    omega3XIntegralKernel φ a b c ≤ t ^ 4 := by
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < b := by linarith [hb.1]
  have hc0 : 0 < c := by linarith [hc.1]
  have hden : (1 / t) * (1 / t) ^ 2 * (1 / t) ≤ a * b ^ 2 * c := by
    gcongr
  have hden' : 1 ≤ t ^ 4 * (a * b ^ 2 * c) := by
    have hh := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ t ^ 4)
    have he : t ^ 4 * ((1 / t) * (1 / t) ^ 2 * (1 / t)) = 1 := by
      field_simp
    rwa [he] at hh
  unfold omega3XIntegralKernel
  apply (div_le_iff₀ (by positivity : 0 < a * b ^ 2 * c)).mpr
  exact (buchstab_le_one (omega3X_argument_bounds hφ ha hb hc).2.2).trans hden'

private theorem positiveGain_integral_linear (l h : ℝ) :
    (∫ x in l..h, h - x) = (h - l) ^ 2 / 2 := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => -(h-x)^2 / 2) (h-x) x := by
    convert ((((hasDerivAt_const x h).sub (hasDerivAt_id x)).pow 2).neg.div_const 2) using 1 <;> norm_num <;> rfl
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ uIcc l h) => hd x)
    ((continuous_const.sub continuous_id).intervalIntegrable l h)
  convert hi using 1
  simp
  ring

private theorem positiveGain_integral_square (l h : ℝ) :
    (∫ x in l..h, (h - x)^2) = (h - l) ^ 3 / 3 := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => -(h-x)^3 / 3) ((h-x)^2) x := by
    convert ((((hasDerivAt_const x h).sub (hasDerivAt_id x)).pow 3).neg.div_const 3) using 1 <;> norm_num <;> rfl
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ uIcc l h) => hd x)
    (((continuous_const.sub continuous_id).pow 2).intervalIntegrable l h)
  convert hi using 1
  simp
  ring

/-- The ordered simplex, not an enclosing cube, supplies the factor one sixth. -/
theorem positiveGain_integral_le_simplex {s t φ : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) (hφ : 2 ≤ φ) :
    omega3XIntegral s t φ ≤ t ^ 4 * (1 / s - 1 / t)^3 / 6 := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  let l := 1 / t
  let h := 1 / s
  have hl : 1 / 10 ≤ l := one_div_le_one_div_of_le ht0 ht
  have hh : h ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hs
  have hlh : l ≤ h := one_div_le_one_div_of_le hs0 hst
  have hinner (a : ℝ) (ha : a ∈ Icc l h) (b : ℝ) (hb : b ∈ Icc a h) :
      (∫ c in b..h, omega3XIntegralKernel φ a b c) ≤ (h-b) * t^4 := by
    calc
      _ ≤ ∫ _c in b..h, t^4 := by
        apply intervalIntegral.integral_mono_on hb.2
          (omega3XIntegralKernel_intervalIntegrable (hl.trans ha.1)
            ((hl.trans ha.1).trans hb.1) hb.2)
          (continuous_const.intervalIntegrable _ _)
        intro c hc
        exact positiveGain_kernel_le hφ ht0
          ⟨hl.trans ha.1, ha.2.trans hh⟩
          ⟨(hl.trans ha.1).trans hb.1, hb.2.trans hh⟩
          ⟨((hl.trans ha.1).trans hb.1).trans hc.1, hc.2.trans hh⟩
          ha.1 (ha.1.trans hb.1) ((ha.1.trans hb.1).trans hc.1)
      _ = _ := by simp
  have hmiddle (a : ℝ) (ha : a ∈ Icc l h) :
      (∫ b in a..h, ∫ c in b..h, omega3XIntegralKernel φ a b c) ≤
        (h-a)^2 / 2 * t^4 := by
    calc
      _ ≤ ∫ b in a..h, (h-b)*t^4 :=
        intervalIntegral.integral_mono_on ha.2
          (omega3XIntegral_inner_intervalIntegrable (hl.trans ha.1) ha.2)
          ((by fun_prop : Continuous (fun b : ℝ => (h-b)*t^4)).intervalIntegrable _ _)
          (hinner a ha)
      _ = _ := by rw [intervalIntegral.integral_mul_const, positiveGain_integral_linear]
  change (∫ a in l..h, ∫ b in a..h, ∫ c in b..h,
    omega3XIntegralKernel φ a b c) ≤ t^4*(h-l)^3/6
  calc
    _ ≤ ∫ a in l..h, (h-a)^2/2*t^4 :=
      intervalIntegral.integral_mono_on hlh
        (omega3XIntegral_middle_intervalIntegrable hl hlh)
        ((by fun_prop : Continuous (fun a : ℝ => (h-a)^2/2*t^4)).intervalIntegrable _ _)
        hmiddle
    _ = (∫ a in l..h, (h-a)^2) * (t^4/2) := by
      rw [← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr
      intro a _
      ring
    _ = _ := by rw [positiveGain_integral_square]; ring

/-- An explicit analytic envelope for every phi>=2; no numerical truncation. -/
theorem positiveGain_envelope_le_simplex {s t : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    omega3XIntegralEnvelope s t ≤ t^4*(1/s-1/t)^3/6 := by
  apply csSup_le
  · exact ⟨omega3XIntegral s t 2, mem_image_of_mem _ (show (2 : ℝ) ∈ Ici 2 by simp)⟩
  · rintro y ⟨φ, hφ, rfl⟩
    exact positiveGain_integral_le_simplex hs hst ht hφ

end Wu2008DoubleSieve
