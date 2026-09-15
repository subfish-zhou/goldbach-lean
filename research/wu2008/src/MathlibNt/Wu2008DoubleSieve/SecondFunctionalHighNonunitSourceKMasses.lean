import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitClosedQuadrature

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real HighNonunitLegal
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical

/-- The complete closed prime word at the actual supported scale and phi. -/
noncomputable def sourceClosedK (N d : ℕ) (δ : ℝ)
    (p : SecondFunctionalParameters) (high : Bool) : ℝ :=
  if high then
    closedPrimeK21 ((N:ℝ)^(1/2-δ)/d) (1/p.kappa3) (1/p.s) (omega3XPhi N d δ)
  else
    closedPrimeK20 ((N:ℝ)^(1/2-δ)/d) (1/p.kappa2) (1/p.kappa3) (1/p.s)
      (omega3XPhi N d δ)

/-- No supremum: retain the same actual phi for both complete words. -/
noncomputable def sourceLegalK (N d : ℕ) (δ : ℝ)
    (p : SecondFunctionalParameters) (high : Bool) : ℝ :=
  if high then K21 (1/p.kappa3) (1/p.s) (omega3XPhi N d δ)
  else K20 (1/p.kappa2) (1/p.kappa3) (1/p.s) (omega3XPhi N d δ)

noncomputable def sourceClosedKMass (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (high : Bool) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      ((N:ℝ)/d/log ((N:ℝ)^(1/2-δ)/d)) * sourceClosedK N d δ p high

noncomputable def sourceLegalKMass (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (high : Bool) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      ((N:ℝ)/d/log ((N:ℝ)^(1/2-δ)/d)) * sourceLegalK N d δ p high

/-- The original Theta weights with the paired actual K payload, without averaging or division. -/
noncomputable def sourceKTheta (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * wuSingularSeries (d*N) /
        ((Nat.totient d : ℝ) * log ((N:ℝ)^(1/2-δ)/d))) *
          (sourceLegalK N d δ p false + sourceLegalK N d δ p true)

end Wu2008DoubleSieve.HighNonunit
