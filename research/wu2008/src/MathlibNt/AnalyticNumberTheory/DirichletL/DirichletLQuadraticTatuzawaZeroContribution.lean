import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticTatuzawaMultiplicativeValueTransfer
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticFunctionalEquation

/-!
# Zero contributions in the four-factor quadratic argument

This file supplies the algebraic/analytic bearing between a completed-function
explicit formula and the positive four-factor logarithmic derivative.  Infinite
zero families are represented by genuine summable kernels.  The finite
rectangle formulation is also exposed, so a later Hadamard-product theorem can
enter through finite rectangles without any opaque “source” predicate.
-/

open Complex Filter Finset
open scoped BigOperators Topology

namespace AnalyticNumberTheory.LargeSieve
namespace TatuzawaZeroContribution

noncomputable section

/-- The real contribution of a zero `ρ` to a logarithmic derivative at a real
point `σ`. -/
def zeroKernel (σ : ℝ) (ρ : ℂ) : ℝ := (((σ : ℂ) - ρ)⁻¹).re

/-- A finite-rectangle zero contribution.  Multiplicity is represented by the
indexing type, so repeated zeros are retained. -/
def finiteZeroContribution {ι : Type*} (zeros : ι → ℂ) (S : Finset ι) (σ : ℝ) : ℝ :=
  ∑ ρ ∈ S, zeroKernel σ (zeros ρ)

/-- The global zero contribution, indexed with multiplicity.  Identifying it
with a convergent sum requires `Summable`; nonnegativity holds without it. -/
def zeroContribution {ι : Type*} (zeros : ι → ℂ) (σ : ℝ) : ℝ :=
  ∑' ρ, zeroKernel σ (zeros ρ)

lemma zeroKernel_ofReal {σ β : ℝ} (h : β < σ) :
    zeroKernel σ (β : ℂ) = 1 / (σ - β) := by
  rw [zeroKernel, ← ofReal_sub, inv_re]
  simp only [ofReal_re, normSq_ofReal]
  field_simp [ne_of_gt (sub_pos.mpr h)]

lemma zeroKernel_nonneg {σ : ℝ} {ρ : ℂ} (hρ : ρ.re ≤ σ) :
    0 ≤ zeroKernel σ ρ := by
  rw [zeroKernel, inv_re]
  exact div_nonneg (sub_nonneg.mpr hρ) (normSq_nonneg _)


/-- Genuine convergence of finite zero rectangles to the zero contribution.
This is `HasSum`, hence a limit over the directed system of finite subsets. -/
theorem hasSum_finiteZeroContribution {ι : Type*} (zeros : ι → ℂ) (σ : ℝ)
    (hsum : Summable (fun ρ ↦ zeroKernel σ (zeros ρ))) :
    HasSum (fun ρ ↦ zeroKernel σ (zeros ρ)) (zeroContribution zeros σ) := by
  simpa only [zeroContribution] using hsum.hasSum







end
end TatuzawaZeroContribution
end AnalyticNumberTheory.LargeSieve
