import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleUnitNegligible
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFiniteDensity

namespace Wu2008DoubleSieve.LowerTripleGrouped
open LowerTripleGroupedFinite
open Finset Real
open scoped Classical

/-- Only the finite Buchstab main remains: the original unit mass is proved small,
not deleted. Both half-error budgets use the same original Theta. -/
theorem source_six_buchstab_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N
      let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)
      (∀ j : Fin 6, (sourceFamily N δ Δ V p j).primeMass ≤
        finiteBuchstabMain N δ Δ V p j * A + ε*Θ) ∧
      (∑ j : Fin 6, (sourceFamily N δ Δ V p j).primeMass) ≤
        (∑ j : Fin 6, finiteBuchstabMain N δ Δ V p j) * A + ε*Θ := by
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hA : 0 < A := mul_pos (mul_pos (by linarith)
    (by positivity)) (div_pos (by norm_num) (by linarith))
  obtain ⟨T0,hT0,h0⟩ := source_six_finite_density k hδ hδhi hρ (half_pos hε)
  obtain ⟨T1,_,h1⟩ := unitMass_six_negligible k hδ hδhi (div_pos hε hA)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp hs
  have hN4 := hT0.trans ((le_max_left T0 T1).trans hN)
  have hC : 0 ≤ wuSingularSeries N / log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have ha := h0 N ((le_max_left _ _).trans hN) hn i Δ V hb p hp hs
  have hu := h1 N ((le_max_right _ _).trans hN) i Δ V hb p hp hs
  have hc := mul_le_mul_of_nonneg_left
    (HighUnitSource.reciprocalMass_theta_payment hN4 hδ hδhi hb) hε.le
  have hcancel : (ε/A) * ((N:ℝ)/log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) *
      (A * (wuSingularSeries N/log N)) =
      ε * (wuSingularSeries N/log N * ((N:ℝ)/log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) := by
    field_simp
  have join (x u b : ℝ)
      (hx : x ≤ (u+b) * (A * wuSingularSeries N/log N) +
        (ε/2)*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V))
      (hu : u ≤ (ε/A)*((N:ℝ)/log N)*
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) :
      x ≤ b * (A * wuSingularSeries N/log N) +
        ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
    have hh := mul_le_mul_of_nonneg_right hu (mul_nonneg hA.le hC)
    rw [hcancel] at hh
    rw [mul_div_assoc] at hx ⊢
    rw [add_mul] at hx
    linarith
  exact ⟨fun j => join _ _ _ (ha.1 j) (hu.1 j), join _ _ _ ha.2 hu.2⟩

end Wu2008DoubleSieve.LowerTripleGrouped
