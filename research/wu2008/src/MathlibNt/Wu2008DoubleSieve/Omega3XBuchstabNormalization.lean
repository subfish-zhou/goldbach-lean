import MathlibNt.Wu2008DoubleSieve.Omega3XGeometryCompact
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniform

/-!
# The literal finite Buchstab main sum for the switched X

Wu04, TeX2215--2238. The ordered prime labels, closed p3 endpoint and
convolution multiplicity are unchanged. This is not a triple integral.
-/

namespace Wu2008DoubleSieve

open Finset Real LiLiuPrereqBuchstab
open scoped Classical

noncomputable def omega3XBuchstabMain {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    ∑ p ∈ omega3XPrimes N δ s t d,
      let x := omega3XScale N d p.1 p.2.1 p.2.2
      x * buchstab (log x / log p.2.1) / log p.2.1

theorem omega3X_buchstab_coordinates {x y : ℝ} (hy : 1 < y) (hyx : y ≤ x) :
    0 < log x ∧ 0 < log y ∧ 1 ≤ log x / log y ∧
      y = x ^ (1 / (log x / log y)) ∧
      (log x / log y) * buchstab (log x / log y) * x / log x =
        x * buchstab (log x / log y) / log y := by
  have hx : 1 < x := hy.trans_le hyx
  have hlx := log_pos hx
  have hly := log_pos hy
  have hu : 1 ≤ log x / log y := by
    apply (le_div_iff₀ hly).mpr
    simpa using log_le_log (by linarith : 0 < y) hyx
  refine ⟨hlx, hly, hu, ?_, ?_⟩
  · rw [rpow_def_of_pos (by linarith : 0 < x)]
    have he : log x * (1 / (log x / log y)) = log y := by
      field_simp
    rw [he, exp_log (by linarith : 0 < y)]
  · field_simp

theorem omega3X_buchstab_main_term_bounds {x y : ℝ}
    (hy : 1 < y) (hyx : y ≤ x) :
    0 < x * buchstab (log x / log y) / log y ∧
      x * buchstab (log x / log y) / log y ≤ x / log y := by
  obtain ⟨_, hly, hu, _, _⟩ := omega3X_buchstab_coordinates hy hyx
  have hx : 0 < x := by linarith
  have hw := buchstab_pos hu
  refine ⟨by positivity, ?_⟩
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right hx.le (buchstab_le_one hu)) hly.le

end Wu2008DoubleSieve
