import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFiniteErrorPayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleRoughDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitMassTheta

namespace Wu2008DoubleSieve.LowerTripleGrouped
open LowerTripleGroupedFinite
open Finset Real
open scoped Classical

/-- Original prime sources, retaining the full unit and finite Buchstab main terms.
The varying singular series is retained on both main terms; only the error uses
the reciprocal-mass bound by Theta/2. The explicit domain 2 ≤ s is implied by
the original mother hypothesis 2 < s. No main term is declared negligible. -/
theorem source_six_finite_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N
      let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)
      (∀ j : Fin 6, (sourceFamily N δ Δ V p j).primeMass ≤
        (unitMass N δ Δ V p j + finiteBuchstabMain N δ Δ V p j) * A + ε*Θ) ∧
      (∑ j : Fin 6, (sourceFamily N δ Δ V p j).primeMass) ≤
        ((∑ j : Fin 6, unitMass N δ Δ V p j) +
          (∑ j : Fin 6, finiteBuchstabMain N δ Δ V p j)) * A + ε*Θ := by
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hA : 0 < A := mul_pos (mul_pos (by linarith)
    (by positivity)) (div_pos (by norm_num) (by linarith))
  obtain ⟨T0,hT0,h0⟩ := source_rough_density k hδ hδhi hρ (half_pos hε)
  obtain ⟨T1,_,h1⟩ := rough_mass_six_finite_paid k hδ hδhi (div_pos hε hA)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp hs
  have hN4 := hT0.trans ((le_max_left T0 T1).trans hN)
  have hC : 0 ≤ wuSingularSeries N / log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have ha := h0 N ((le_max_left _ _).trans hN) hn i Δ V hb p hp
  have hraw := h1 N ((le_max_right _ _).trans hN) i Δ V hb p hp hs
  have hc := mul_le_mul_of_nonneg_left
    (HighUnitSource.reciprocalMass_theta_payment hN4 hδ hδhi hb) hε.le
  have hcancel : (ε/A) * ((N:ℝ)/log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) *
      (A * (wuSingularSeries N/log N)) =
      ε * (wuSingularSeries N/log N * ((N:ℝ)/log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) := by
    field_simp
  have join (x r b : ℝ)
      (hx : x ≤ r * (A * wuSingularSeries N/log N) +
        (ε/2)*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V))
      (hr : r ≤ b + (ε/A)*((N:ℝ)/log N)*
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) :
      x ≤ b * (A * wuSingularSeries N/log N) +
        ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
    have hh := mul_le_mul_of_nonneg_right hr (mul_nonneg hA.le hC)
    simp only [add_mul] at hh
    rw [hcancel] at hh
    rw [mul_div_assoc] at hx ⊢
    linarith
  exact ⟨fun j => join _ _ _ (ha.1 j) (hraw.1 j), join _ _ _ ha.2 hraw.2⟩

end Wu2008DoubleSieve.LowerTripleGrouped
