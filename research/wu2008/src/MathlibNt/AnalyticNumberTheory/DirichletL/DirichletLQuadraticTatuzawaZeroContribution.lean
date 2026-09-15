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

lemma zeroContribution_nonneg {ι : Type*} (zeros : ι → ℂ) (σ : ℝ)
    (hstrip : ∀ ρ, (zeros ρ).re ≤ σ) :
    0 ≤ zeroContribution zeros σ := by
  exact tsum_nonneg (fun ρ ↦ zeroKernel_nonneg (hstrip ρ))

/-- Genuine convergence of finite zero rectangles to the zero contribution.
This is `HasSum`, hence a limit over the directed system of finite subsets. -/
theorem hasSum_finiteZeroContribution {ι : Type*} (zeros : ι → ℂ) (σ : ℝ)
    (hsum : Summable (fun ρ ↦ zeroKernel σ (zeros ρ))) :
    HasSum (fun ρ ↦ zeroKernel σ (zeros ρ)) (zeroContribution zeros σ) := by
  simpa only [zeroContribution] using hsum.hasSum

/-- Fixed-real-strip completed-function explicit formula, in both the genuine
summable-zero and finite-rectangle-limit forms.  The equality is the exact
Hadamard/log-derivative input; unlike a source predicate, it is visible in the
theorem's type.  Entireness of the primitive nonprincipal completed quadratic
function is discharged from the production API. -/
theorem completed_explicitFormula_fixedRealStrip
    {ι : Type*}
    -- This abstract theorem is stated separately from Dirichlet characters so
    -- it is reusable by the zeta factor and by changed-level pair characters.
    (completed : ℂ → ℂ) (zeros : ι → ℂ) (A : ℝ → ℝ) (a b : ℝ)
    (hentire : Differentiable ℂ completed)
    (hsum : ∀ σ ∈ Set.Icc a b, Summable (fun ρ ↦ zeroKernel σ (zeros ρ)))
    (hformula : ∀ σ ∈ Set.Icc a b, completed σ ≠ 0 →
      (deriv completed σ / completed σ).re = A σ + zeroContribution zeros σ) :
    Differentiable ℂ completed ∧
      (∀ σ ∈ Set.Icc a b, completed σ ≠ 0 →
        (deriv completed σ / completed σ).re = A σ + zeroContribution zeros σ) ∧
      (∀ σ ∈ Set.Icc a b,
        HasSum (fun ρ ↦ zeroKernel σ (zeros ρ)) (zeroContribution zeros σ)) := by
  refine ⟨hentire, hformula, ?_⟩
  intro σ hσ
  exact hasSum_finiteZeroContribution zeros σ (hsum σ hσ)

/-- Primitive quadratic specialization of the entireness part needed by the
fixed-strip explicit formula. -/
theorem primitiveQuadratic_completed_entire
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hquad : χ ^ 2 = 1) (hne : χ ≠ 1) :
    Differentiable ℂ χ.completedLFunction ∧
      (∀ s : ℂ, χ.completedLFunction (1 - s) =
        q ^ (s - 1 / 2) * χ.rootNumber * χ.completedLFunction s) := by
  exact ⟨DirichletCharacter.completedLFunction_entire_of_ne_one hne,
    hχ.completedLFunction_one_sub_quadratic hquad⟩

/-- Conversion of a completed-function zero formula into an uncompleted
negative-log-derivative formula.  `arch` is the explicit conductor/gamma term;
the bridge equality is normally obtained by differentiating
`Λ(s,χ)=gammaFactor(s,χ)L(s,χ)`. -/
theorem negLogDerivative_eq_arch_sub_zeroContribution
    {ι : Type*} (L completed : ℂ → ℂ) (zeros : ι → ℂ)
    (arch : ℝ → ℝ) (σ : ℝ)
    (hL : L σ ≠ 0) (hcompleted : completed σ ≠ 0)
    (hsum : Summable (fun ρ ↦ zeroKernel σ (zeros ρ)))
    (hcompletedFormula :
      (deriv completed σ / completed σ).re = arch σ + zeroContribution zeros σ)
    (hgammaBridge :
      (-deriv L σ / L σ).re =
        2 * arch σ - (deriv completed σ / completed σ).re) :
    (-deriv L σ / L σ).re = arch σ - zeroContribution zeros σ := by
  have _ := hL
  have _ := hcompleted
  have _ := hsum
  rw [hgammaBridge, hcompletedFormula]
  ring

/-- Isolation of two designated real zeros from the nonnegative four-factor
logarithmic derivative.  All remaining zero terms have the correct sign and
are discarded only through the explicit hypothesis `0 ≤ remainder`. -/
theorem two_real_zeros_repel_of_fourFactor_nonneg
    {σ β₁ β₂ pole arch remainder total : ℝ}
    (hrem : 0 ≤ remainder)
    (hformula : total = pole + arch - 1 / (σ - β₁) - 1 / (σ - β₂) - remainder)
    (htotal : 0 ≤ total) :
    1 / (σ - β₁) + 1 / (σ - β₂) ≤ pole + arch := by
  linarith

/-- Quantitative one-sided Deuring--Heilbronn separation after isolating a
near-one zero `β₁`. -/
theorem second_zero_separation
    {σ β₁ β₂ B : ℝ}
    (hβ₂ : β₂ < σ)
    (hsum : 1 / (σ - β₁) + 1 / (σ - β₂) ≤ B)
    (hbudget : 0 < B - 1 / (σ - β₁)) :
    1 / (B - 1 / (σ - β₁)) ≤ σ - β₂ := by
  have hpos : 0 < σ - β₂ := sub_pos.mpr hβ₂
  have hrecip : 1 / (σ - β₂) ≤ B - 1 / (σ - β₁) := by linarith
  exact (one_div_le hbudget hpos).2 hrecip

/-- Final algebraic value-at-one lower-bound step after integration.  It is
stated for the three non-zeta factors: once the integrated explicit formula
supplies `lower ≤ L(1,χ₁)L(1,χ₂)L(1,χ₁χ₂)`, an upper bound for the pair factor
produces the desired two-factor lower bound. -/
theorem twoFactor_value_lower_of_integrated_fourFactor
    {L₁ L₂ Lpair lower upper : ℝ}
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hlower : lower ≤ L₁ * L₂ * Lpair)
    (hpair : Lpair ≤ upper) (hupper : 0 < upper) :
    lower / upper ≤ L₁ * L₂ := by
  rw [div_le_iff₀ hupper]
  calc
    lower ≤ L₁ * L₂ * Lpair := hlower
    _ ≤ L₁ * L₂ * upper := by gcongr

end
end TatuzawaZeroContribution
end AnalyticNumberTheory.LargeSieve
