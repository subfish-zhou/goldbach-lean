import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitKThetaJoinedSource

namespace Wu2008DoubleSieve.HighSourcePayload
open Finset Real
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The unchanged source mass with a literal supported-d payload. -/
noncomputable def mass (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      ((N:ℝ)/d/log ((N:ℝ)^(1/2-δ)/d)) * f d

/-- Original Theta weights, with no division by their total mass. -/
noncomputable def theta (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ) (f : ℕ → ℝ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * wuSingularSeries (d*N) /
        ((Nat.totient d : ℝ) * log ((N:ℝ)^(1/2-δ)/d))) * f d

noncomputable def unitPair (N d : ℕ) (δ : ℝ) (p : SecondFunctionalParameters) : ℝ :=
  HighUnit.J20 (1/p.kappa2) (1/p.kappa3) (1/p.s) (omega3XPhi N d δ) +
    HighUnit.J21 (1/p.kappa3) (1/p.s) (omega3XPhi N d δ)

/-- All four integrals retain the very same supported d and actual phi. -/
noncomputable def paired (N d : ℕ) (δ : ℝ) (p : SecondFunctionalParameters) : ℝ :=
  unitPair N d δ p +
    (HighNonunit.sourceLegalK N d δ p false + HighNonunit.sourceLegalK N d δ p true)

noncomputable def unitTheta (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) : ℝ := theta N δ Δ V (fun d => unitPair N d δ p)

noncomputable def pairedTheta (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) : ℝ := theta N δ Δ V (fun d => paired N d δ p)

/-- Exact bookkeeping; no envelope or supremum is used. -/
theorem pairedTheta_eq (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) :
    pairedTheta N δ Δ V p = unitTheta N δ Δ V p + HighNonunit.sourceKTheta N δ Δ V p := by
  simp only [pairedTheta, unitTheta, theta, paired, HighNonunit.sourceKTheta,
    mul_add, sum_add_distrib]

/-- The old actual J integrals have exactly the shared original-weight mass. -/
theorem unit_mass_eq_boxed (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) :
    mass N δ Δ V (fun d => unitPair N d δ p) =
      HighUnit.boxedIntegral20 N δ (convolutionWuWindows N Δ V)
        (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
      HighUnit.boxedIntegral21 N δ (convolutionWuWindows N Δ V)
        (fun _ => 1/p.kappa3) (fun _ => 1/p.s) := by
  unfold mass HighUnit.boxedIntegral20 HighUnit.boxedIntegral21
  rw [← mul_add, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro d _
  unfold unitPair
  ring

end Wu2008DoubleSieve.HighSourcePayload
