import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex Filter Topology
open ArithmeticFunction hiding log
open scoped ComplexOrder LSeries.notation

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- In the half-plane of absolute convergence, the product of the Riemann zeta
function and a Dirichlet L-function is the L-series of their Dirichlet
convolution. -/
lemma riemannZeta_mul_LFunction_eq_LSeries_zetaMul
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * χ.LFunction s = LSeries χ.zetaMul s := by
  rw [zetaMul, ← coe_mul, LSeries_convolution']
  · rw [χ.LFunction_eq_LSeries hs]
    congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · exact LSeries_congr χ.apply_eq_toArithmeticFunction_apply s
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      ZMod.LSeriesSummable_of_one_lt_re χ hs

/-- A nonprincipal quadratic Dirichlet L-function has nonnegative real value at
`1`.  The proof approaches `1` along the real axis from the right and uses the
nonnegative Dirichlet coefficients of `ζ(s) L(s, χ)`. -/
theorem LFunction_apply_one_nonneg_of_sq_eq_one
    {χ : DirichletCharacter ℂ N} (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    0 ≤ χ.LFunction 1 := by
  have habs : LSeries.abscissaOfAbsConv χ.zetaMul ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      fun _ hy ↦ χ.LSeriesSummable_zetaMul hy
  have hseries_pos {x : ℝ} (hx : 1 < x) : 0 < LSeries χ.zetaMul x := by
    apply LSeries.positive (zetaMul_nonneg hquad)
      (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one)
    exact habs.trans_lt (by exact_mod_cast hx)
  have hprod_pos {x : ℝ} (hx : 1 < x) :
      0 < ((x : ℂ) - 1) * riemannZeta x * χ.LFunction x := by
    rw [mul_assoc, riemannZeta_mul_LFunction_eq_LSeries_zetaMul χ (by simpa using hx)]
    exact mul_pos (by exact_mod_cast sub_pos.mpr hx) (hseries_pos hx)
  have hcoe_nhds : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hcoe_punctured :
      Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hcoe_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxne : (x : ℂ) ≠ 1 := by
      exact_mod_cast ne_of_gt hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hxne
  have hlim :
      Tendsto (fun x : ℝ ↦ ((x : ℂ) - 1) * riemannZeta x * χ.LFunction x)
        (𝓝[>] (1 : ℝ)) (𝓝 (χ.LFunction 1)) := by
    simpa only [Function.comp_apply, one_mul] using
      (riemannZeta_residue_one.comp hcoe_punctured).mul
        ((χ.differentiableAt_LFunction 1 (.inr hχ)).continuousAt.tendsto.comp hcoe_nhds)
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hprod_pos hx).le

/-- A nonprincipal quadratic Dirichlet L-function is real at `1`. -/
theorem LFunction_apply_one_im_eq_zero_of_sq_eq_one
    {χ : DirichletCharacter ℂ N} (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    (χ.LFunction 1).im = 0 :=
  (Complex.nonneg_iff.mp (LFunction_apply_one_nonneg_of_sq_eq_one hquad hχ)).2.symm

/-- A nonprincipal quadratic Dirichlet L-function has strictly positive real
part at `1`. -/
theorem LFunction_apply_one_re_pos_of_sq_eq_one
    {χ : DirichletCharacter ℂ N} (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    0 < (χ.LFunction 1).re := by
  have hnonneg := Complex.nonneg_iff.mp
    (LFunction_apply_one_nonneg_of_sq_eq_one hquad hχ)
  have him : (χ.LFunction 1).im = 0 := hnonneg.2.symm
  have hre_ne : (χ.LFunction 1).re ≠ 0 := by
    intro hre
    apply χ.LFunction_apply_one_ne_zero hχ
    apply Complex.ext
    · simpa only [zero_re] using hre
    · simpa only [zero_im] using him
  exact lt_of_le_of_ne hnonneg.1 (Ne.symm hre_ne)

/-- Positivity and realness of a nonprincipal quadratic Dirichlet L-value at
`1`. -/
theorem LFunction_apply_one_positive_real_of_sq_eq_one
    {χ : DirichletCharacter ℂ N} (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    (χ.LFunction 1).im = 0 ∧ 0 < (χ.LFunction 1).re :=
  ⟨LFunction_apply_one_im_eq_zero_of_sq_eq_one hquad hχ,
    LFunction_apply_one_re_pos_of_sq_eq_one hquad hχ⟩

end DirichletCharacter