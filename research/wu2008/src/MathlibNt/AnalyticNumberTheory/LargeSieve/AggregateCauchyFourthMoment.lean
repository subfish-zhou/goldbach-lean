import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

noncomputable section
open Complex Finset
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false
namespace AnalyticNumberTheory.LargeSieve

local instance aggregateCauchyFactFour : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

lemma piLp_four_norm_pow {ι : Type*} [Fintype ι]
    (v : PiLp 4 (fun _ : ι => ℂ)) : ‖v‖ ^ 4 = ∑ i, ‖v i‖ ^ 4 := by
  have : Fact ((1 : ℝ≥0∞) ≤ (4 : ℕ)) := ⟨by norm_num⟩
  rw [PiLp.norm_eq_of_nat (p := (4 : ℝ≥0∞)) 4 (by norm_num)]
  simpa only [one_div] using (Real.rpow_inv_natCast_pow
    (x := ∑ i, ‖v i‖ ^ 4) (n := 4) (by positivity) (by norm_num))

/-- Apply Banach-valued Cauchy once in the finite ℓ⁴ space, not separately
and then bound each coordinate by the entire family. No cardinality loss. -/
theorem aggregate_cauchy_fourth {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ) (s : ℂ) (r B : ℝ) (hr : 0 < r) (hB : 0 ≤ B)
    (hf : ∀ i, Differentiable ℂ (f i))
    (hcircle : ∀ z ∈ Metric.sphere s r, ∑ i, ‖f i z‖ ^ 4 ≤ B) :
    (∑ i, ‖deriv (f i) s‖ ^ 4) ≤ B / r ^ 4 := by
  let e := (PiLp.continuousLinearEquiv 4 ℂ (fun _ : ι => ℂ)).symm
  let F : ℂ → PiLp 4 (fun _ : ι => ℂ) := fun z => e (fun i => f i z)
  have hd : Differentiable ℂ F :=
    e.differentiable.comp (differentiable_pi.mpr hf)
  have hder : deriv F s = e (fun i => deriv (f i) s) := by
    exact (e.hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_pi.mpr fun i => (hf i s).hasDerivAt)).deriv
  have hc : ∀ z ∈ Metric.sphere s r, ‖F z‖ ≤ B ^ ((4 : ℝ)⁻¹) := by
    intro z hz
    have hroot : (B ^ ((4 : ℝ)⁻¹)) ^ 4 = B :=
      Real.rpow_inv_natCast_pow hB (by norm_num)
    have hp : ‖F z‖ ^ 4 ≤ (B ^ ((4 : ℝ)⁻¹)) ^ 4 := by
      rw [hroot, piLp_four_norm_pow]
      exact hcircle z hz
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg hB _) (by norm_num)).mp hp
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd.diffContOnCl hc) 4
  have hroot : (B ^ ((4 : ℝ)⁻¹)) ^ 4 = B :=
    Real.rpow_inv_natCast_pow hB (by norm_num)
  rw [div_pow, hroot, hder, piLp_four_norm_pow] at h
  exact h

/-- Nonnegative scalar weights are absorbed in the ℓ⁴ coordinates before Cauchy. -/
theorem aggregate_weighted_cauchy_fourth {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (s : ℂ) (r B : ℝ) (hr : 0 < r) (hB : 0 ≤ B)
    (hf : ∀ i, Differentiable ℂ (f i))
    (hcircle : ∀ z ∈ Metric.sphere s r, ∑ i, w i * ‖f i z‖ ^ 4 ≤ B) :
    (∑ i, w i * ‖deriv (f i) s‖ ^ 4) ≤ B / r ^ 4 := by
  let a : ι → ℂ := fun i => (w i ^ ((4 : ℝ)⁻¹) : ℝ)
  have ha (i : ι) : ‖a i‖ ^ 4 = w i := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (hw i) _)]
    exact Real.rpow_inv_natCast_pow (hw i) (by norm_num)
  have h := aggregate_cauchy_fourth (fun i z => a i * f i z) s r B hr hB
    (fun i => (hf i).const_mul (a i)) (by
      intro z hz
      simpa only [norm_mul, mul_pow, ha] using hcircle z hz)
  simpa only [deriv_const_mul_field, norm_mul, mul_pow, ha] using h

end AnalyticNumberTheory.LargeSieve
