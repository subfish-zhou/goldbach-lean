import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleKThetaNormalization
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleIntegralDensity

namespace Wu2008DoubleSieve.LowerTripleSourceK
open Finset Real
open scoped Classical

/-- Original single and all-six prime masses with the actual-phi true-li main.
Rho is first supplied by normalization, then consumed by the original integral
density producer. Each spends epsilon/2; only T remains in the conclusion. -/
theorem source_six_kTheta_density (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      (∀ j : Fin 6, (LowerTripleGrouped.sourceFamily N δ Δ V p j).primeMass ≤
        (2/(1-2*δ))*sourceKTheta N δ Δ V p j +
          ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) ∧
      (∑ j : Fin 6, (LowerTripleGrouped.sourceFamily N δ Δ V p j).primeMass) ≤
        (2/(1-2*δ))*(∑ j : Fin 6, sourceKTheta N δ Δ V p j) +
          ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have he : 0 < ε/2 := by positivity
  obtain ⟨ρ, hρ, T0, hT0, h0⟩ := integralKMass_theta_density_slack k hδ hδhi he
  obtain ⟨T1, _, h1⟩ := source_six_integral_density k hδ hδhi hρ he
  refine ⟨max T0 T1, hT0.trans (le_max_left _ _), ?_⟩
  intro N hN hn i Δ V hb p hp hs
  have hnorm := h0 N ((le_max_left _ _).trans hN) i Δ V hb p hp hs
  have hsource := h1 N ((le_max_right _ _).trans hN) hn i Δ V hb p hp hs
  dsimp only at hsource
  have hscalar : ∀ x : ℝ,
      x * ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*
        wuSingularSeries N/log N) =
      ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
        (wuSingularSeries N/log N) * x := by intro x; ring
  simp only [hscalar] at hsource
  constructor
  · intro j
    linarith only [hsource.1 j, hnorm.1 j]
  · linarith only [hsource.2, hnorm.2]

end Wu2008DoubleSieve.LowerTripleSourceK
