import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLLocalFiniteDiskExplicitFormula
import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
# Quantitative control of a zero-free local explicit-formula remainder

The derivative estimate below is the Borel--Carathéodory replacement for the
exponentially wasteful Cauchy estimate on `g` itself.  Its input is an actual
holomorphic logarithm `h` of the nonvanishing factor.  Crucially, the numerical
input is the additive oscillation of `log ‖g‖`; no circle maximum/interior
minimum ratio is assumed.
-/

open Complex Metric Set
open scoped Topology

namespace AnalyticNumberTheory.LargeSieve
namespace TatuzawaZeroContribution

noncomputable section

/-- Borel--Carathéodory controls the derivative of a holomorphic logarithm by
its real-part oscillation.  The constant `4` comes from applying the theorem on
the outer disk and Cauchy's estimate on the half-radius circle. -/
theorem norm_deriv_holomorphicLog_le
    (h : ℂ → ℂ) (c : ℂ) {R A : ℝ} (hR : 0 < R) (hA : 0 < A)
    (hh : DifferentiableOn ℂ h (ball c R))
    (hosc : ∀ z ∈ ball c R, (h z).re - (h c).re ≤ A) :
    ‖deriv h c‖ ≤ 4 * A / R := by
  let H : ℂ → ℂ := fun z ↦ h (c + z) - h c
  have hHd : DifferentiableOn ℂ H (ball 0 R) := by
    intro z hz
    have hcz : c + z ∈ ball c R := by
      simpa [mem_ball, dist_comm] using hz
    have hhat : DifferentiableAt ℂ h (c + z) :=
      (hh (c + z) hcz).differentiableAt (isOpen_ball.mem_nhds hcz)
    exact ((hhat.comp z (by fun_prop)).sub
      (differentiableAt_const (h c))).differentiableWithinAt
  have hHre : MapsTo H (ball 0 R) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (h (c + z) - h c).re ≤ A
    simpa [sub_re] using hosc (c + z) (by simpa [mem_ball, dist_comm] using hz)
  have hH0 : H 0 = 0 := by simp [H]
  have hhalf : 0 < R / 2 := by positivity
  have hcircle : ∀ z ∈ sphere 0 (R / 2), ‖H z‖ ≤ 2 * A := by
    intro z hz
    have hznorm : ‖z‖ = R / 2 := by simpa [mem_sphere] using hz
    have hzball : z ∈ ball 0 R := by
      simpa [mem_ball, hznorm] using (half_lt_self hR)
    have hbc := borelCaratheodory_zero hA hHd hHre hR hzball hH0
    rw [hznorm] at hbc
    convert hbc using 1; field_simp; ring
  -- The closed half-radius disk stays inside the holomorphicity domain.
  have hclosure : closure (ball (0 : ℂ) (R / 2)) ⊆ ball 0 R := by
    rw [closure_ball 0 hhalf.ne']
    exact closedBall_subset_ball (half_lt_self hR)
  have hcont : DiffContOnCl ℂ H (ball 0 (R / 2)) :=
    ⟨hHd.mono (ball_subset_ball (half_lt_self hR).le),
      hHd.continuousOn.mono hclosure⟩
  have hcauchy : ‖deriv H 0‖ ≤ (2 * A) / (R / 2) :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hhalf hcont hcircle
  -- Translation and subtraction of a constant preserve the center derivative.
  have hderiv : deriv H 0 = deriv h c := by
    have houter : HasDerivAt h (deriv h c) (c + 0) := by
      simpa using ((hh c (mem_ball_self hR)).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self hR))).hasDerivAt
    have hH : HasDerivAt H (deriv h c) 0 := by
      simpa [H] using
        (houter.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add c)).sub_const (h c)
    exact hH.deriv
  rw [hderiv] at hcauchy
  convert hcauchy using 1; field_simp; ring

/-- If `h` is a holomorphic logarithm of `g`, the preceding additive estimate
is exactly an `O(A/R)` estimate for the nonzero local explicit-formula
remainder `g'/g`. -/
theorem norm_logDeriv_le_of_holomorphicLog_oscillation
    (g h : ℂ → ℂ) (c : ℂ) {R A : ℝ} (hR : 0 < R) (hA : 0 < A)
    (_hg : DifferentiableOn ℂ g (ball c R))
    (hh : DifferentiableOn ℂ h (ball c R))
    (hexp : EqOn (fun z ↦ exp (h z)) g (ball c R))
    (hosc : ∀ z ∈ ball c R, (h z).re - (h c).re ≤ A) :
    ‖logDeriv g c‖ ≤ 4 * A / R := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hgc : g c ≠ 0 := by
    rw [← hexp hc]
    exact exp_ne_zero _
  have hderiv : deriv g c = g c * deriv h c := by
    have hevent : (fun z ↦ exp (h z)) =ᶠ[𝓝 c] g :=
      by filter_upwards [isOpen_ball.mem_nhds hc] with z hz; exact hexp hz
    rw [← hevent.deriv_eq]
    simpa [← hexp hc] using
      ((hh c hc).differentiableAt (isOpen_ball.mem_nhds hc)).hasDerivAt.cexp.deriv
  rw [logDeriv_apply, hderiv, mul_div_cancel_left₀ _ hgc]
  exact norm_deriv_holomorphicLog_le h c hR hA hh hosc

end
end TatuzawaZeroContribution
end AnalyticNumberTheory.LargeSieve
