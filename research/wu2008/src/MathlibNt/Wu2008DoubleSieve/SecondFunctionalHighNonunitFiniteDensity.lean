import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteErrorPayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughDensityJoinedSource

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real
open scoped Classical

/-- The full fixed-delta density multiplies the paid finite main pair.
The original-scale error is separately paid using the genuine varying C(N). -/
theorem actual_source_pair_finite_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      actualSource N δ p (convolutionWuWindows N Δ V) false +
        actualSource N δ p (convolutionWuWindows N Δ V) true ≤
        (finiteBuchstabMain N δ Δ V p false + finiteBuchstabMain N δ Δ V p true) *
          ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*
            wuSingularSeries N/log N) +
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hA : 0 < A := mul_pos (mul_pos (by linarith)
    (by positivity)) (div_pos (by norm_num) (by linarith))
  obtain ⟨T0,hT0,h0⟩ := actual_source_pair_rough_density k hδ hδhi hρ (half_pos hε)
  obtain ⟨T1,_,h1⟩ := rough_mass_pair_finite_paid k hδ hδhi (div_pos hε hA)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb p hp hs
  have hN4 := hT0.trans ((le_max_left T0 T1).trans hN)
  have hC : 0 ≤ wuSingularSeries N / log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have ha := h0 N ((le_max_left _ _).trans hN) he i Δ V hb p hp hs
  have hb' := mul_le_mul_of_nonneg_right
    (h1 N ((le_max_right _ _).trans hN) i Δ V hb p hp hs) (mul_nonneg hA.le hC)
  have hc := mul_le_mul_of_nonneg_left
    (HighUnitSource.reciprocalMass_theta_payment hN4 hδ hδhi hb) hε.le
  have hcancel : (ε/A) * ((N:ℝ)/log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) *
      (A * (wuSingularSeries N/log N)) =
      ε * (wuSingularSeries N/log N * ((N:ℝ)/log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) := by
    field_simp
  simp only [add_mul] at hb'
  rw [hcancel] at hb'
  change _ ≤ _ * (A * wuSingularSeries N / log N) + _ at ha
  change _ ≤ _ * (A * wuSingularSeries N / log N) + _
  rw [mul_div_assoc] at ha ⊢
  linarith

end Wu2008DoubleSieve.HighNonunit

namespace Wu2008DoubleSieve
open Finset Real FourthRowPhiOmega2 HighUnitSource
open scoped Classical

/-- The physical five-Phi consumer now contains the paid full5/full6 finite main pair,
with its full fixed-delta density and a single epsilon Theta. -/
theorem secondFunctional_high_nonunit_finite_density_joined_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (hS : 3 ≤ p.S) (hS5 : p.S ≤ 5)
    (k : ℕ) (hk : 1 ≤ k) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
            4 * wuImprovementLimit true δ p.S - wuImprovementLimit true δ p.kappa1 -
            J δ p.s p.S - J δ p.kappa2 p.S - J δ p.kappa3 p.S +
            (2/(1-2*δ)) * (unitLogCap20 (1/p.kappa2) (1/p.kappa3) (1/p.s) +
              unitLogCap21 (1/p.kappa3) (1/p.s)) + ε) *
              boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) +
          secondFunctionalLowerGammaLedger p N δ (convolutionWuWindows N Δ V) +
          (HighNonunit.finiteBuchstabMain N δ Δ V p false +
            HighNonunit.finiteBuchstabMain N δ Δ V p true) *
            (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
              wuSingularSeries N / log N) := by
  obtain ⟨T0,hT0,hbase⟩ := secondFunctional_high_unit_theta_joined_source p hp hs hs3 hS hS5
    k hk hδ hδhi (half_pos hε)
  obtain ⟨T1,_,hdensity⟩ := HighNonunit.actual_source_pair_finite_density k hδ
    (by linarith) hρ (half_pos hε)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb
  have h0 := hbase N ((le_max_left T0 T1).trans hN) he i Δ V hb
  have h1 := hdensity N ((le_max_right T0 T1).trans hN) he i Δ V hb p hp hs.le
  simp only [HighNonunit.actualSource, HighNonunit.word, Bool.false_eq_true, ↓reduceIte] at h1
  unfold secondFunctionalHighNonunitGammaLedger at h0
  unfold secondFunctionalLowerGammaLedger
  nlinarith only [h0,h1]

end Wu2008DoubleSieve
