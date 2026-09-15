import SigmaSimpleResidueExpansion

noncomputable section
namespace SigmaSimpleResiduePrimitive
open Polynomial Complex Set
open scoped BigOperators

theorem rootKernel_eq_re (z w : ℂ) (t : ℝ) :
    SigmaRationalOuterFTC.rootKernel z.re z.im w.re w.im t =
      (w / ((t : ℂ)-z)).re := by
  simp only [SigmaRationalOuterFTC.rootKernel, Complex.div_re,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.normSq_apply]
  ring

theorem root_quadratic_ne (B : ℝ[X]) (t : ℝ) (ht : B.eval t ≠ 0)
    (z : ℂ) (hz : z ∈ (B.map Complex.ofRealHom).roots.toFinset) :
    (t-z.re)^2+z.im^2 ≠ 0 := by
  have hB : B ≠ 0 := by intro h; simp [h] at ht
  have hr := (mem_roots (map_ne_zero hB)).mp (Multiset.mem_toFinset.mp hz)
  have hn : (t : ℂ)-z ≠ 0 := by
    intro he
    have h : (B.map Complex.ofRealHom).eval (t : ℂ) = 0 := by
      rw [sub_eq_zero.mp he]
      exact hr
    rw [eval_complex_map, Complex.ofReal_eq_zero] at h
    exact ht h
  have hp := Complex.normSq_pos.mpr hn
  have he : Complex.normSq ((t : ℂ)-z) = (t-z.re)^2+z.im^2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [he] at hp
  exact hp.ne'

/-- The actual residue primitive differentiates to the entire proper rational function. -/
theorem simplePrimitive_deriv (R B : ℝ[X]) (hB : B.Separable)
    (hR : R.degree < B.degree) (t : ℝ) (ht : B.eval t ≠ 0) :
    HasDerivAt (simplePrimitive R B) (R.eval t / B.eval t) t := by
  classical
  have hd := HasDerivAt.sum (u := (B.map Complex.ofRealHom).roots.toFinset)
    (fun z hz => SigmaRationalOuterFTC.rootPrimitive_deriv z.re z.im
      (residue R B z).re (residue R B z).im t (root_quadratic_ne B t ht z hz))
  have hf := congrArg Complex.re (simple_fraction R B hB hR t ht)
  simp only [Complex.ofReal_re, Complex.re_sum, ← rootKernel_eq_re] at hf
  rw [← hf] at hd
  convert hd using 1 <;> first | rfl | skip
  funext x
  simp only [simplePrimitive, Finset.sum_apply]

end SigmaSimpleResiduePrimitive
