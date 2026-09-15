import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleRawDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleExceptionPayment

namespace Wu2008DoubleSieve.LowerTripleGrouped
open Finset Real
open scoped Classical

/-- Original prime masses reach canonical rough RAW masses after the exception budget. -/
theorem source_rough_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N
      let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)
      (∀ j : Fin 6, (sourceFamily N δ Δ V p j).primeMass ≤
        (roughFamily N δ Δ V p j).mass * A + ε*Θ) ∧
      (∑ j : Fin 6, (sourceFamily N δ Δ V p j).primeMass) ≤
        (∑ j : Fin 6, (roughFamily N δ Δ V p j).mass) * A + ε*Θ := by
  obtain ⟨T0,hT0,hpuri⟩ := source_prime_purification k hδ hδhi (half_pos hε)
  obtain ⟨T1,_,hsingle⟩ := source_restricted_prime_density k hδ hδhi hρ (half_pos hε)
  obtain ⟨T2,_,hsix⟩ := source_restricted_prime_six_density k hδ hδhi hρ (half_pos hε)
  refine ⟨max T0 (max T1 T2),hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp
  have hN0 := (le_max_left T0 _).trans hN
  have hN12 := (le_max_right T0 _).trans hN
  have hu := hpuri N hN0 i Δ V hb p hp
  constructor
  · intro j
    have hd := hsingle N ((le_max_left T1 T2).trans hN12) hn i Δ V hb p hp j profileRough
    have hj := hu.1 j
    change (roughFamily N δ Δ V p j).primeMass ≤ _ at hd
    simp only [roughFamily] at hj hd ⊢
    linarith
  · have hd := hsix N ((le_max_right T1 T2).trans hN12) hn i Δ V hb p hp (fun _ => profileRough)
    have hj := hu.2
    change (∑ j : Fin 6, (roughFamily N δ Δ V p j).primeMass) ≤ _ at hd
    simp only [roughFamily] at hj hd ⊢
    linarith

end Wu2008DoubleSieve.LowerTripleGrouped
