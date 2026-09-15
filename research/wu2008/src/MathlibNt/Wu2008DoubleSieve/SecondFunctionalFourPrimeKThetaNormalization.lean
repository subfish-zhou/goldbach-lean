import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeSourceKMasses
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighPayloadNormalization

namespace Wu2008DoubleSieve.FourPrimeNonunit
open FourPrimeContinuous Finset Real
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical

/-- The actual mother hypotheses supply all four compact endpoints. -/
theorem legalK_mother_compact (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    CompactParameters (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) := by
  have hs0 : 0 < p.s := by linarith
  have h30 : 0 < p.kappa3 := hs0.trans_le hp.s_le_kappa3
  have h20 : 0 < p.kappa2 := h30.trans hp.kappa3_lt_kappa2
  have h10 : 0 < p.kappa1 := h20.trans hp.kappa2_lt_kappa1
  exact ⟨one_div_le_one_div_of_le h10 (hp.kappa1_le_S.trans hp.S_le_ten),
    one_div_le_one_div_of_le h20 hp.kappa2_lt_kappa1.le,
    one_div_le_one_div_of_le h30 hp.kappa3_lt_kappa2.le,
    one_div_le_one_div_of_le hs0 hp.s_le_kappa3,
    one_div_le_one_div_of_le (by norm_num) hs⟩

/-- The cap is independent of phi, including empty legal domains. -/
theorem legalK_bounds {b c e f : ℝ} (hp : CompactParameters b c e f)
    (phi : ℝ) (j : Fin 4) :
    0 ≤ legalK b c e f phi j ∧ legalK b c e f phi j ≤ 10*(4:ℝ)^4 := by
  have h16 := K16_bounds hp phi
  have h17 := K17_bounds hp phi
  have h18 := K18_bounds hp phi
  have h19 := K19_bounds hp phi
  have hall : ∀ j : Fin 4,
      0 ≤ legalK b c e f phi j ∧ legalK b c e f phi j ≤ 10*(4:ℝ)^4 := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    exact ⟨h16, h17, h18, h19⟩
  exact hall j

theorem sourceLegalK_bounds (N d : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 4) :
    0 ≤ sourceLegalK N d δ p j ∧ sourceLegalK N d δ p j ≤ 10*(4:ℝ)^4 :=
  legalK_bounds (legalK_mother_compact p hp hs) (omega3XPhi N d δ) j

/-- One common cap covers the sum, without changing any leading kernel. -/
theorem sourceLegalK_sum_bounds (N d : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    0 ≤ ∑ j, sourceLegalK N d δ p j ∧
      (∑ j, sourceLegalK N d δ p j) ≤ 4*10*(4:ℝ)^4 := by
  constructor
  · exact sum_nonneg fun j _ => (sourceLegalK_bounds N d δ p hp hs j).1
  · calc
      _ ≤ ∑ _j : Fin 4, 10*(4:ℝ)^4 :=
        sum_le_sum fun j _ => (sourceLegalK_bounds N d δ p hp hs j).2
      _ = _ := by norm_num

/-- Exact finite distributivity at the unchanged original source weights. -/
theorem sourceLegalKMass_sum (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) :
    HighSourcePayload.mass N δ Δ V (fun d => ∑ j, sourceLegalK N d δ p j) =
      ∑ j, sourceLegalKMass N δ Δ V p j := by
  unfold HighSourcePayload.mass sourceLegalKMass
  simp only [HighSourcePayload.mass, mul_sum]
  exact sum_comm

/-- The true li factor and actual totient weights distribute, not by definition. -/
theorem sourceKTheta_sum (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) :
    HighSourcePayload.theta N δ Δ V (fun d => ∑ j, sourceLegalK N d δ p j) =
      ∑ j, sourceKTheta N δ Δ V p j := by
  unfold HighSourcePayload.theta sourceKTheta
  simp only [HighSourcePayload.theta, mul_sum]
  exact sum_comm

/-- Explicit original mass, with the actual supported-d phi in every K. -/
theorem sourceLegalKMass_literal (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) :
    sourceLegalKMass N δ Δ V p j =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ((N:ℝ)/d/log ((N:ℝ)^(1/2-δ)/d)) *
            legalK (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s)
              (omega3XPhi N d δ) j := rfl

/-- No totient substitution, envelope, or normalized probability weights. -/
theorem sourceKTheta_literal (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) :
    sourceKTheta N δ Δ V p j = 4 * logarithmicIntegral N *
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          wuSingularSeries (d*N) /
            ((Nat.totient d : ℝ)*log ((N:ℝ)^(1/2-δ)/d))) *
          legalK (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s)
            (omega3XPhi N d δ) j := rfl

/-- Genuine support-weight nonnegativity and the original-Theta cap.
This uses the same generic normalization API; the cap pays errors only. -/
theorem sourceLegalK_mass_theta_bounds {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 4) :
    0 ≤ sourceLegalKMass N δ Δ V p j ∧
      0 ≤ sourceKTheta N δ Δ V p j ∧
      sourceKTheta N δ Δ V p j ≤ 10*(4:ℝ)^4 *
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  exact ⟨HighSourcePayload.mass_nonneg hN hδ hδhi hb
      (fun d _ => (sourceLegalK_bounds N d δ p hp hs j).1),
    HighSourcePayload.theta_bounds hN hδ hδhi hb
      (fun d _ => sourceLegalK_bounds N d δ p hp hs j)⟩

/-- A single positive rho and threshold precede N, boxes, mother parameters and j.
The fixed delta loss and original li/Theta weights are retained. The all-four
estimate spends epsilon once, rather than summing four individual errors. -/
theorem sourceLegalKMass_theta_density_slack (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      (∀ j : Fin 4,
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
          (wuSingularSeries N/log N) * sourceLegalKMass N δ Δ V p j ≤
        (2/(1-2*δ))*sourceKTheta N δ Δ V p j +
          epsilon*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) ∧
      (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
          (wuSingularSeries N/log N) * (∑ j, sourceLegalKMass N δ Δ V p j) ≤
        (2/(1-2*δ))*(∑ j, sourceKTheta N δ Δ V p j) +
          epsilon*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) := by
  obtain ⟨ρ, hr, T, hT4, hT⟩ :=
    HighSourcePayload.mass_theta_density_slack k hδ hδhi
      (show 0 ≤ 4*10*(4:ℝ)^4 by positivity) he
  refine ⟨ρ, hr, T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  constructor
  · intro j
    apply hT N hN i Δ V hb (fun d => sourceLegalK N d δ p j)
    intro d _
    have h := sourceLegalK_bounds N d δ p hp hs j
    exact ⟨h.1, h.2.trans (by norm_num)⟩
  · have h := hT N hN i Δ V hb (fun d => ∑ j, sourceLegalK N d δ p j)
      (fun d _ => sourceLegalK_sum_bounds N d δ p hp hs)
    rwa [sourceLegalKMass_sum, sourceKTheta_sum] at h

end Wu2008DoubleSieve.FourPrimeNonunit
