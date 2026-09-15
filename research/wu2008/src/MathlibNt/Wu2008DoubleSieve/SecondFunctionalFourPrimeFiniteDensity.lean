import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeFiniteErrorPayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteDensity

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset Real
open scoped Classical

/-- Original prime sources, with full fixed-delta-rho finite Buchstab density.
The genuine varying singular series is paid only on the error, using Theta. -/
theorem source_four_finite_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N
      let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)
      (∀ j : Fin 4, (sourceFamily N δ Δ V p j).primeMass ≤
        finiteBuchstabMain N δ Δ V p j * A + ε*Θ) ∧
      (∑ j : Fin 4, (sourceFamily N δ Δ V p j).primeMass) ≤
        (∑ j : Fin 4, finiteBuchstabMain N δ Δ V p j) * A + ε*Θ := by
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hA : 0 < A := mul_pos (mul_pos (by linarith)
    (by positivity)) (div_pos (by norm_num) (by linarith))
  obtain ⟨T0,hT0,h0⟩ := source_rough_density k hδ hδhi hρ (half_pos hε)
  obtain ⟨T1,_,h1⟩ := rough_mass_four_finite_paid k hδ hδhi (div_pos hε hA)
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

/-- The actual original mother source consumes every paid finite word. -/
theorem mother_source_four_finite_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ j : Fin 4,
      actualSource N δ p (convolutionWuWindows N Δ V) j ≤ finiteBuchstabMain N δ Δ V p j *
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N) +
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hd⟩ := source_four_finite_density k hδ hδhi hρ hε
  refine ⟨T,hT,?_⟩
  intro N hN hn i Δ V hb p hp hs j
  have ha := actual_source_le (N := N) (δ := δ) p (convolutionWuWindows N Δ V)
    (fun d h => (omega3_source_support_le_Q (by have := hT.trans hN; omega) hδ hδhi hb h).1)
    (hT.trans hN) hn j
  have hj := (hd N hN hn i Δ V hb p hp hs).1 j
  rw [(sourceFamily_dictionary N δ Δ V p j).1] at hj
  exact ha.trans hj

end Wu2008DoubleSieve.FourPrimeNonunit
