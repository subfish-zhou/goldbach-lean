import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLLocalExplicitFormulaLogRemainder
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLActualFourFactorLocalZeroRepulsion
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Holomorphic logarithms of the character-specific local factor

The logarithm in this file is not an additional hypothesis.  It is constructed
from a primitive of `g'/g` on the (convex, hence simply connected) disk and is
normalised at the centre.  The exponential identity is then proved by showing
that `exp h / g` has zero derivative on the disk.
-/

open Complex Metric Set
open scoped Topology

namespace AnalyticNumberTheory.LargeSieve
namespace TatuzawaZeroContribution

noncomputable section

/-- A nonvanishing holomorphic function on a disk has a holomorphic logarithm
on that disk.  This is the disk-specialised, differentiable version of the
continuous lifting theorem for the exponential covering map. -/
theorem exists_holomorphicLog_on_ball
    (g : ℂ → ℂ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball c R))
    (hg0 : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h (ball c R) ∧
      EqOn (fun z ↦ exp (h z)) g (ball c R) := by
  let U : Set ℂ := ball c R
  have hc : c ∈ U := mem_ball_self hR
  have hlogDeriv : DifferentiableOn ℂ (fun z ↦ deriv g z / g z) U :=
    (hg.deriv isOpen_ball).div hg hg0
  obtain ⟨h, hhc, hh'⟩ :=
    hlogDeriv.isExactOn_ball.with_val_at c (log (g c))
  have hh : DifferentiableOn ℂ h U := fun z hz ↦
    (hh' z hz).differentiableAt.differentiableWithinAt
  let F : ℂ → ℂ := fun z ↦ exp (h z) / g z
  have hF : DifferentiableOn ℂ F U := hh.cexp.div hg hg0
  have hFderiv : ∀ z ∈ U, deriv F z = 0 := by
    intro z hz
    have hgd : DifferentiableAt ℂ g z :=
      (hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)
    have hde : deriv (fun w ↦ exp (h w)) z =
        exp (h z) * (deriv g z / g z) := by
      simpa only [(hh' z hz).deriv] using (hh' z hz).cexp.deriv
    rw [show deriv F z = deriv (fun w ↦ exp (h w) / g w) z by rfl,
      deriv_fun_div (hh' z hz).differentiableAt.cexp hgd (hg0 z hz), hde]
    field_simp [hg0 z hz]
    ring
  have hFc : F c = 1 := by
    have hgc : g c ≠ 0 := hg0 c hc
    simp [F, hhc, exp_log hgc, hgc]
  have hconst : EqOn F (fun _ : ℂ ↦ 1) U :=
    isOpen_ball.eqOn_of_deriv_eq isPreconnected_ball hF (differentiableOn_const 1)
      (fun z hz ↦ by simp [hFderiv z hz]) hc hFc
  refine ⟨h, hh, ?_⟩
  intro z hz
  have hzconst := hconst hz
  change exp (h z) / g z = 1 at hzconst
  exact (div_eq_one_iff_eq (hg0 z hz)).mp hzconst

/-- The local factor selected by the actual character finite-disk
factorisation has a genuinely constructed holomorphic logarithm. -/
theorem CharacterLocalDiskData.exists_holomorphicLog
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {c : ℂ} {R : ℝ}
    (d : CharacterLocalDiskData χ c R) (hR : 0 < R) :
    ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h (ball c R) ∧
      EqOn (fun z ↦ exp (h z)) d.g (ball c R) :=
  exists_holomorphicLog_on_ball d.g c hR d.g_analytic.differentiableOn d.g_ne_zero

/-- For the logarithm just constructed, its derivative is literally the
character-specific finite-disk remainder `g'/g` at every point of the disk. -/
theorem CharacterLocalDiskData.exists_holomorphicLog_deriv_eq_logDeriv
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {c : ℂ} {R : ℝ}
    (d : CharacterLocalDiskData χ c R) (hR : 0 < R) :
    ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h (ball c R) ∧
      EqOn (fun z ↦ exp (h z)) d.g (ball c R) ∧
      ∀ z ∈ ball c R, deriv h z = logDeriv d.g z := by
  obtain ⟨h, hh, hexp⟩ := d.exists_holomorphicLog hR
  refine ⟨h, hh, hexp, ?_⟩
  intro z hz
  have hhd : DifferentiableAt ℂ h z :=
    (hh z hz).differentiableAt (isOpen_ball.mem_nhds hz)
  have hevent : (fun w ↦ exp (h w)) =ᶠ[𝓝 z] d.g :=
    hexp.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)
  have hderiv : deriv h z * d.g z = deriv d.g z := by
    rw [← hexp hz, ← hevent.deriv_eq]
    simpa only [mul_comm] using hhd.hasDerivAt.cexp.deriv.symm
  rw [logDeriv_apply]
  exact (eq_div_iff (d.g_ne_zero z hz)).2 hderiv

end
end TatuzawaZeroContribution
end AnalyticNumberTheory.LargeSieve