import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFiniteToClosedK
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleSourceKPayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleShiftedBoundaryDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleBuchstabDensity

namespace Wu2008DoubleSieve.LowerTripleSourceK
open Finset Real LowerTripleGroupedFinite LowerTripleGroupedBoundary
open scoped Classical

/-- The explicitly retained finite carrier is the actual unshifted main. -/
theorem unshifted_le_closedKMass {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6) :
    unshiftedFiniteBuchstabMain N δ Δ V p j ≤ closedKMass N δ Δ V p j := by
  simpa only [unshiftedFiniteBuchstabMain, mainWeight, closedKMass, sourceClosedK] using
    filtered_finiteBuchstabMain_le_closedPrimeKj hN hδ hδhi hb p hp hs j

theorem unshifted_six_le_closedKMass {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    (∑ j : Fin 6, unshiftedFiniteBuchstabMain N δ Δ V p j) ≤
      ∑ j : Fin 6, closedKMass N δ Δ V p j :=
  sum_le_sum (fun j _ => unshifted_le_closedKMass hN hδ hδhi hb p hp hs j)

/-- Original prime mass reaches actual-phi integrals. Unit, shifted finite atoms
and quadrature are paid by their actual producers with one total error. -/
theorem source_six_integral_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N
      let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)
      (∀ j : Fin 6, (LowerTripleGrouped.sourceFamily N δ Δ V p j).primeMass ≤
        integralKMass N δ Δ V p j * A + ε*Θ) ∧
      (∑ j : Fin 6, (LowerTripleGrouped.sourceFamily N δ Δ V p j).primeMass) ≤
        (∑ j : Fin 6, integralKMass N δ Δ V p j) * A + ε*Θ := by
  have he : 0 < ε/3 := by positivity
  obtain ⟨T0,hT0,h0⟩ := LowerTripleGrouped.source_six_buchstab_density k hδ hδhi hρ he
  obtain ⟨T1,_,h1⟩ := finiteMain_six_boundary_density_paid k hδ hδhi hρ he
  obtain ⟨T2,_,h2⟩ := closedKMass_six_density k hδ hδhi hρ he
  refine ⟨max T0 (max T1 T2), hT0.trans (le_max_left _ _), ?_⟩
  intro N hN hn i Δ V hb p hp hs
  have hN0 := (le_max_left T0 (max T1 T2)).trans hN
  have hN1 := (le_max_left T1 T2).trans ((le_max_right T0 (max T1 T2)).trans hN)
  have hN2 := (le_max_right T1 T2).trans ((le_max_right T0 (max T1 T2)).trans hN)
  have hN4 := hT0.trans hN0
  have hc := h0 N hN0 hn i Δ V hb p hp hs
  have hbnd := h1 N hN1 i Δ V hb p hp hs
  have hquad := h2 N hN2 i Δ V hb p hp hs
  have hA : 0 ≤ (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*
      wuSingularSeries N/log N := by
    have hden : 0 < 1-2*δ := by linarith
    have hlog : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
    have hC := wuSingularSeries_pos N (by omega)
    positivity
  constructor
  · intro j
    have hg := mul_le_mul_of_nonneg_right (unshifted_le_closedKMass hN4 hδ hδhi hb p hp hs j) hA
    linarith only [hc.1 j, hbnd.1 j, hg, hquad.1 j]
  · have hg := mul_le_mul_of_nonneg_right (unshifted_six_le_closedKMass hN4 hδ hδhi hb p hp hs) hA
    linarith only [hc.2, hbnd.2, hg, hquad.2]

end Wu2008DoubleSieve.LowerTripleSourceK
