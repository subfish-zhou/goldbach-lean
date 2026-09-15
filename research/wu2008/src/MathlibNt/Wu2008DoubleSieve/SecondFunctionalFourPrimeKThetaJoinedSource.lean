import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeFiniteToClosedK
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeSourceKPayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeKThetaNormalization
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalZeroWidthJoinedSource

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset Real
open scoped Classical

/-- The actual prime families consume the full finite-to-integral chain.
Rho is selected before all source data and eliminated only through its paid slack. -/
theorem source_four_kTheta (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)
      (∀ j : Fin 4, (sourceFamily N δ Δ V p j).primeMass ≤
        (2/(1-2*δ))*sourceKTheta N δ Δ V p j + ε*Θ) ∧
      (∑ j : Fin 4, (sourceFamily N δ Δ V p j).primeMass) ≤
        (2/(1-2*δ))*(∑ j : Fin 4, sourceKTheta N δ Δ V p j) + ε*Θ := by
  have he : 0 < ε/3 := by positivity
  obtain ⟨ρ,hρ,T0,hT0,hnorm⟩ := sourceLegalKMass_theta_density_slack k hδ hδhi he
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hD : 0 < 1-2*δ := by linarith
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨T1,_,hfinite⟩ := source_four_finite_density k hδ hδhi hρ he
  obtain ⟨T2,_,hquad⟩ := sourceClosedKMass_four_theta k hδ hδhi hA he
  refine ⟨max T0 (max T1 T2),hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp hs
  have hN0 := (le_max_left T0 _).trans hN
  have hN12 := (le_max_right T0 _).trans hN
  have hN4 := hT0.trans hN0
  let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)
  let C := A * (wuSingularSeries N/log N)
  have hC : 0 ≤ C := mul_nonneg hA (div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le)
  have hf := hfinite N ((le_max_left T1 T2).trans hN12) hn i Δ V hb p hp hs
  have hq := hquad N ((le_max_right T1 T2).trans hN12) i Δ V hb p hp hs
  have hu := hnorm N hN0 i Δ V hb p hp hs
  have join (x F K L U : ℝ)
      (hx : x ≤ F * (A * wuSingularSeries N/log N) + (ε/3)*Θ)
      (hFK : F ≤ K) (hKL : C*|K-L| ≤ (ε/3)*Θ)
      (hU : C*L ≤ (2/(1-2*δ))*U + (ε/3)*Θ) :
      x ≤ (2/(1-2*δ))*U + ε*Θ := by
    have hstep := mul_le_mul_of_nonneg_right hFK hC
    have hdiff := mul_le_mul_of_nonneg_left (le_abs_self (K-L)) hC
    rw [mul_div_assoc] at hx
    change x ≤ F*C + (ε/3)*Θ at hx
    nlinarith only [hx,hstep,hdiff,hKL,hU]
  constructor
  · intro j
    exact join _ _ _ _ _ (hf.1 j)
      (finiteBuchstabMain_le_sourceClosedKMass hN4 hδ hδhi hb p hp hs j)
      (hq.1 j) (hu.1 j)
  · exact join _ _ _ _ _ hf.2
      (finiteBuchstabMain_all4_le_sourceClosedKMass hN4 hδ hδhi hb p hp hs)
      hq.2.2 hu.2

/-- Every original source, and the complete four-source sum, have one epsilon budget. -/
theorem mother_source_four_kTheta (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) W
      (∀ j : Fin 4, actualSource N δ p W j ≤
        (2/(1-2*δ))*sourceKTheta N δ Δ V p j + ε*Θ) ∧
      (∑ j : Fin 4, actualSource N δ p W j) ≤
        (2/(1-2*δ))*(∑ j : Fin 4, sourceKTheta N δ Δ V p j) + ε*Θ := by
  obtain ⟨T,hT,hd⟩ := source_four_kTheta k hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN hn i Δ V hb p hp hs
  have hle (j : Fin 4) : actualSource N δ p (convolutionWuWindows N Δ V) j ≤
      (sourceFamily N δ Δ V p j).primeMass := by
    rw [(sourceFamily_dictionary N δ Δ V p j).1]
    exact actual_source_le (N := N) (δ := δ) p (convolutionWuWindows N Δ V)
      (fun d h => (omega3_source_support_le_Q (by have := hT.trans hN; omega) hδ hδhi hb h).1)
      (hT.trans hN) hn j
  have h := hd N hN hn i Δ V hb p hp hs
  exact ⟨fun j => (hle j).trans (h.1 j), (sum_le_sum (fun j _ => hle j)).trans h.2⟩

end Wu2008DoubleSieve.FourPrimeNonunit

namespace Wu2008DoubleSieve.SecondFunctionalZeroWidth
open Finset Real FourthRowPhiOmega2
open scoped Classical

/-- The original zero-width mother now consumes the actual K16 Theta payload.
The explicit nine-term ledger, fixed delta and single epsilon remain unchanged. -/
theorem kTheta_joined_source
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (heq : p.kappa3 = p.s)
    (hs : 2 < p.s) (hs3 : p.s ≤ 3) (hS : 3 ≤ p.S) (hS5 : p.S ≤ 5)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
            4 * wuImprovementLimit true δ p.S - wuImprovementLimit true δ p.kappa1 -
            J δ p.s p.S - J δ p.kappa2 p.S - J δ p.kappa3 p.S + ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
          (retained p N δ (convolutionWuWindows N Δ V) +
            (2/(1-2*δ))*FourPrimeNonunit.sourceKTheta N δ Δ V p 0) := by
  obtain ⟨T0,hT0,hbase⟩ := joined_source p hp heq hs hs3 hS hS5
    k hk hδ hδhi (half_pos hε)
  obtain ⟨T1,_,hK⟩ := FourPrimeNonunit.source_four_kTheta k hδ (by linarith) (half_pos hε)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb
  have h0 := hbase N ((le_max_left _ _).trans hN) he i Δ V hb
  have h1 := (hK N ((le_max_right _ _).trans hN) he i Δ V hb p hp hs.le).1 0
  rw [(FourPrimeNonunit.sourceFamily_dictionary N δ Δ V p 0).1] at h1
  nlinarith only [h0,h1]

/-- Regression on the actual row3 record, not a surrogate tuple. -/
theorem row3_kTheta_joined_source (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) SecondFunctionalParameters.row3.s ≤
          (4 * wuUpperCoefficient SecondFunctionalParameters.row3.S + wuUpperCoefficient SecondFunctionalParameters.row3.kappa1 -
            4 * wuImprovementLimit true δ SecondFunctionalParameters.row3.S - wuImprovementLimit true δ SecondFunctionalParameters.row3.kappa1 -
            J δ SecondFunctionalParameters.row3.s SecondFunctionalParameters.row3.S - J δ SecondFunctionalParameters.row3.kappa2 SecondFunctionalParameters.row3.S - J δ SecondFunctionalParameters.row3.kappa3 SecondFunctionalParameters.row3.S + ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
          (retained SecondFunctionalParameters.row3 N δ (convolutionWuWindows N Δ V) +
            (2/(1-2*δ))*FourPrimeNonunit.sourceKTheta N δ Δ V SecondFunctionalParameters.row3 0) := by
  exact kTheta_joined_source SecondFunctionalParameters.row3 SecondFunctionalParameters.row3_motherAdmissible
    SecondFunctionalParameters.row3_last_eq
    (by norm_num [SecondFunctionalParameters.row3]) (by norm_num [SecondFunctionalParameters.row3])
    (by norm_num [SecondFunctionalParameters.row3]) (by norm_num [SecondFunctionalParameters.row3]) k hk hδ hδhi hε

/-- Regression on the actual row4 record, not a surrogate tuple. -/
theorem row4_kTheta_joined_source (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) SecondFunctionalParameters.row4.s ≤
          (4 * wuUpperCoefficient SecondFunctionalParameters.row4.S + wuUpperCoefficient SecondFunctionalParameters.row4.kappa1 -
            4 * wuImprovementLimit true δ SecondFunctionalParameters.row4.S - wuImprovementLimit true δ SecondFunctionalParameters.row4.kappa1 -
            J δ SecondFunctionalParameters.row4.s SecondFunctionalParameters.row4.S - J δ SecondFunctionalParameters.row4.kappa2 SecondFunctionalParameters.row4.S - J δ SecondFunctionalParameters.row4.kappa3 SecondFunctionalParameters.row4.S + ε) *
              boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) +
          (retained SecondFunctionalParameters.row4 N δ (convolutionWuWindows N Δ V) +
            (2/(1-2*δ))*FourPrimeNonunit.sourceKTheta N δ Δ V SecondFunctionalParameters.row4 0) := by
  exact kTheta_joined_source SecondFunctionalParameters.row4 SecondFunctionalParameters.row4_motherAdmissible
    SecondFunctionalParameters.row4_last_eq
    (by norm_num [SecondFunctionalParameters.row4]) (by norm_num [SecondFunctionalParameters.row4])
    (by norm_num [SecondFunctionalParameters.row4]) (by norm_num [SecondFunctionalParameters.row4]) k hk hδ hδhi hε

end Wu2008DoubleSieve.SecondFunctionalZeroWidth
