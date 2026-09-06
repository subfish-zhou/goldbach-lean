import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace AnalyticNumberTheory.LargeSieve

/-- The complex Laplace moment used in the Mellin transform of Chen's kernel. -/
def chenLaplaceMoment (q : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  Complex.exp (-q * u) * (u : ℂ) ^ n

/-- Integrability of the complex Laplace moment in the right half-plane. -/
theorem integrableOn_chenLaplaceMoment {q : ℂ} (hq : 0 < q.re) (n : ℕ) :
    IntegrableOn (chenLaplaceMoment q n) (Ioi 0) := by
  have hm : AEStronglyMeasurable (chenLaplaceMoment q n)
      (volume.restrict (Ioi 0)) := by
    apply Continuous.aestronglyMeasurable
    unfold chenLaplaceMoment
    fun_prop
  apply (MeasureTheory.integrable_norm_iff hm).mp
  have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (n : ℝ)) (b := q.re)
      (by have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
      (by norm_num) hq
  apply hreal.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [chenLaplaceMoment, norm_mul, Complex.norm_exp, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos hu, ← Real.rpow_natCast, Real.rpow_one]
  ring

/-- The elementary complex Laplace moment formula
`∫₀∞ exp (-q u) uⁿ du = n! / qⁿ⁺¹`, valid for `re q > 0`. -/
theorem integral_chenLaplaceMoment {q : ℂ} (hq : 0 < q.re) (n : ℕ) :
    ∫ u : ℝ in Ioi 0, chenLaplaceMoment q n u =
      (n.factorial : ℂ) / q ^ (n + 1) := by
  induction n with
  | zero =>
      rw [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
      simp only [chenLaplaceMoment, pow_zero, mul_one]
      rw [integral_exp_mul_complex_Ioi (a := -q) (by simpa) 0]
      simp
  | succ n ih =>
      have hq0 : q ≠ 0 := by
        intro h
        simp [h] at hq
      let F : ℝ → ℂ := fun u => Complex.exp (-q * u) * (u : ℂ) ^ (n + 1)
      let F' : ℝ → ℂ := fun u =>
        -q * chenLaplaceMoment q (n + 1) u + (n + 1 : ℂ) * chenLaplaceMoment q n u
      have hderiv : ∀ u : ℝ, HasDerivAt F (F' u) u := by
        intro u
        dsimp [F, F', chenLaplaceMoment]
        have hc : HasDerivAt (fun z : ℂ => Complex.exp (-q * z) * z ^ (n + 1))
            ((-q * Complex.exp (-q * (u : ℂ))) * (u : ℂ) ^ (n + 1) +
              Complex.exp (-q * (u : ℂ)) * ((n + 1 : ℂ) * (u : ℂ) ^ n))
            (u : ℂ) := by
          convert! (((hasDerivAt_id (u : ℂ)).const_mul (-q)).cexp.mul
            (hasDerivAt_pow (n + 1) (u : ℂ))) using 1
          simp only [id_eq, Nat.cast_add, Nat.cast_one, add_comm (n : ℕ) 1]
          rw [show 1 + n - 1 = n by omega]
          ring
        convert! hc.comp_ofReal using 1; ring
      have hFint : IntegrableOn F (Ioi 0) := by
        change IntegrableOn (chenLaplaceMoment q (n + 1)) (Ioi 0)
        exact integrableOn_chenLaplaceMoment hq (n + 1)
      have hleft : IntegrableOn (fun u => -q * chenLaplaceMoment q (n + 1) u) (Ioi 0) :=
        (integrableOn_chenLaplaceMoment hq (n + 1)).const_mul (-q)
      have hright : IntegrableOn (fun u => (n + 1 : ℂ) * chenLaplaceMoment q n u) (Ioi 0) :=
        (integrableOn_chenLaplaceMoment hq n).const_mul (n + 1 : ℂ)
      have hF'int : IntegrableOn F' (Ioi 0) := hleft.add hright
      have hlim : Tendsto F atTop (𝓝 0) :=
        MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
          (fun u _ => hderiv u) hF'int hFint
      have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
        (a := (0 : ℝ)) (m := (0 : ℂ)) (fun u _ => hderiv u) hF'int hlim
      rw [show (∫ u : ℝ in Ioi 0, F' u) =
          (∫ u : ℝ in Ioi 0, -q * chenLaplaceMoment q (n + 1) u) +
            ∫ u : ℝ in Ioi 0, (n + 1 : ℂ) * chenLaplaceMoment q n u by
        exact integral_add hleft hright] at hFTC
      simp only [integral_const_mul, F, Complex.ofReal_zero,
        zero_pow (Nat.succ_ne_zero n), mul_zero, sub_zero] at hFTC
      rw [ih] at hFTC
      rw [show ∫ u : ℝ in Ioi 0, chenLaplaceMoment q (n + 1) u =
          (n + 1 : ℂ) * ((n.factorial : ℂ) / q ^ (n + 1)) / q by
        apply (eq_div_iff hq0).2
        linear_combination -hFTC]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

end AnalyticNumberTheory.LargeSieve
