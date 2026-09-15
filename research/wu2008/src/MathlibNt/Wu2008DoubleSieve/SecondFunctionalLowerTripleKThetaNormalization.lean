import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleSourceKQuadrature
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighPayloadNormalization

namespace Wu2008DoubleSieve.LowerTripleSourceK
open Finset Real LowerTripleContinuous
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical

/-- True-li Theta of the six original integrals, at the actual supported-d phi. -/
noncomputable def sourceKTheta (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  HighSourcePayload.theta N δ Δ V (fun d => sourceIntegralK N d δ p j)

/-- Literal source weights: sigma once, C(dN), original totient, true li and phi. -/
theorem sourceKTheta_literal (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) :
    sourceKTheta N δ Δ V p j = 4 * logarithmicIntegral N *
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          wuSingularSeries (d*N) /
            ((Nat.totient d : ℝ)*log ((N:ℝ)^(1/2-δ)/d))) *
          K (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s)
            j (omega3XPhi N d δ) := rfl

/-- Exact denominator reassociation, including totalized zero denominators. -/
theorem integralKMass_eq_mass (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) :
    integralKMass N δ Δ V p j =
      HighSourcePayload.mass N δ Δ V (fun d => sourceIntegralK N d δ p j) := by
  unfold integralKMass HighSourcePayload.mass
  simp only [div_mul_eq_div_div]

/-- The mother domain supplies the cap without imposing any new phi hypothesis. -/
theorem sourceIntegralK_bounds (N d : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6) :
    0 ≤ sourceIntegralK N d δ p j ∧ sourceIntegralK N d δ p j ≤ 10*(4:ℝ)^3 :=
  K_bounds (mother_compact_parameters p hp hs) j (omega3XPhi N d δ)

/-- A common cap for the whole six-payload sum pays errors only. -/
theorem sourceIntegralK_sum_bounds (N d : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    0 ≤ ∑ j, sourceIntegralK N d δ p j ∧
      (∑ j, sourceIntegralK N d δ p j) ≤ 6*10*(4:ℝ)^3 := by
  constructor
  · exact sum_nonneg fun j _ => (sourceIntegralK_bounds N d δ p hp hs j).1
  · calc
      _ ≤ ∑ _j : Fin 6, 10*(4:ℝ)^3 :=
        sum_le_sum fun j _ => (sourceIntegralK_bounds N d δ p hp hs j).2
      _ = _ := by norm_num

/-- Exact finite distribution of the actual, unnormalized integral mass. -/
theorem integralKMass_sum (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) :
    HighSourcePayload.mass N δ Δ V (fun d => ∑ j, sourceIntegralK N d δ p j) =
      ∑ j, integralKMass N δ Δ V p j := by
  simp only [integralKMass_eq_mass, HighSourcePayload.mass, mul_sum]
  exact sum_comm

/-- True-li and totient-weighted Theta distribute without changing the source. -/
theorem sourceKTheta_sum (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) :
    HighSourcePayload.theta N δ Δ V (fun d => ∑ j, sourceIntegralK N d δ p j) =
      ∑ j, sourceKTheta N δ Δ V p j := by
  unfold HighSourcePayload.theta sourceKTheta
  simp only [HighSourcePayload.theta, mul_sum]
  exact sum_comm

/-- Original mass and Theta signs; the compact cap never replaces the main term. -/
theorem sourceIntegralK_mass_theta_bounds {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6) :
    0 ≤ integralKMass N δ Δ V p j ∧
      0 ≤ sourceKTheta N δ Δ V p j ∧
      sourceKTheta N δ Δ V p j ≤ 10*(4:ℝ)^3 *
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  rw [integralKMass_eq_mass]
  exact ⟨HighSourcePayload.mass_nonneg hN hδ hδhi hb
      (fun d _ => (sourceIntegralK_bounds N d δ p hp hs j).1),
    HighSourcePayload.theta_bounds hN hδ hδhi hb
      (fun d _ => sourceIntegralK_bounds N d δ p hp hs j)⟩

/-- The sixfold mass and Theta retain their original signs and a zero-safe cap. -/
theorem sourceIntegralK_six_mass_theta_bounds {i k N : ℕ} {δ Δ : ℝ}
    {V : Fin i → ℝ} (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    0 ≤ (∑ j, integralKMass N δ Δ V p j) ∧
      0 ≤ (∑ j, sourceKTheta N δ Δ V p j) ∧
      (∑ j, sourceKTheta N δ Δ V p j) ≤ 6*10*(4:ℝ)^3 *
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  rw [← integralKMass_sum, ← sourceKTheta_sum]
  exact ⟨HighSourcePayload.mass_nonneg hN hδ hδhi hb
      (fun d _ => (sourceIntegralK_sum_bounds N d δ p hp hs).1),
    HighSourcePayload.theta_bounds hN hδ hδhi hb
      (fun d _ => sourceIntegralK_sum_bounds N d δ p hp hs)⟩

/-- One rho precedes T, N, boxes, all mother parameters and all six labels.
The all-six estimate consumes the summed payload once, spending epsilon once. -/
theorem integralKMass_theta_density_slack (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      (∀ j : Fin 6,
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
          (wuSingularSeries N/log N) * integralKMass N δ Δ V p j ≤
        (2/(1-2*δ))*sourceKTheta N δ Δ V p j +
          epsilon*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) ∧
      (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
          (wuSingularSeries N/log N) * (∑ j, integralKMass N δ Δ V p j) ≤
        (2/(1-2*δ))*(∑ j, sourceKTheta N δ Δ V p j) +
          epsilon*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) := by
  obtain ⟨ρ, hr, T, hT4, hT⟩ :=
    HighSourcePayload.mass_theta_density_slack k hδ hδhi
      (show 0 ≤ 6*10*(4:ℝ)^3 by positivity) he
  refine ⟨ρ, hr, T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  constructor
  · intro j
    rw [integralKMass_eq_mass]
    apply hT N hN i Δ V hb (fun d => sourceIntegralK N d δ p j)
    intro d _
    have h := sourceIntegralK_bounds N d δ p hp hs j
    exact ⟨h.1, h.2.trans (by norm_num)⟩
  · have h := hT N hN i Δ V hb (fun d => ∑ j, sourceIntegralK N d δ p j)
      (fun d _ => sourceIntegralK_sum_bounds N d δ p hp hs)
    rwa [integralKMass_sum, sourceKTheta_sum] at h

end Wu2008DoubleSieve.LowerTripleSourceK
