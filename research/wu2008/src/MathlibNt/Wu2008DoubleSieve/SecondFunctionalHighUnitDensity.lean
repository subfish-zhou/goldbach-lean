import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitR1
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitErrorPayment
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitSieve
open Real Finset HighUnitSource

/-- The actual filtered pair has the original unfiltered mass and one total error.
The fixed-delta density factor is retained verbatim. -/
theorem mother_envelope_pair_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ)^(1/2-δ)
      let R := fun d : ℕ => Q/d
      let a2 := fun _ : ℕ => 1/p.kappa2
      let a3 := fun _ : ℕ => 1/p.kappa3
      let b := fun _ : ℕ => 1/p.s
      HighUnitPrimeOutput.envelope20 N W R a2 a3 b +
        HighUnitPrimeOutput.envelope21 N W R a3 b ≤
        (HighUnit.boxedSigma20 N δ W a2 a3 b + HighUnit.boxedSigma21 N δ W a3 b) *
          (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
            wuSingularSeries N / log N) + ε*boxTheta N Q W := by
  have heps : 0 < ε/2 := by positivity
  obtain ⟨T0,hT0,hpaid⟩ := mother_prime_pair_R2_small_paid k hδ hδhi heps
  obtain ⟨T1,_,hR1⟩ := mother_R1_sieve_relative k hδ hδhi heps
  obtain ⟨T2,_,hden⟩ := omega3_source_rosser_density hδ hδhi hρ
  refine ⟨max T0 (max T1 T2), hT0.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb p hp hs
  have hN0 := (le_max_left T0 _).trans hN
  have hN1 := (le_max_left T1 T2).trans ((le_max_right T0 _).trans hN)
  have hN2 := (le_max_right T1 T2).trans ((le_max_right T0 _).trans hN)
  have hf := hpaid N hN0 i Δ V hb p hp hs heven
  have hr := hR1 N hN1 i Δ V hb p
  have hx : 0 ≤ HighUnit.boxedSigma20 N δ (convolutionWuWindows N Δ V)
      (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
      HighUnit.boxedSigma21 N δ (convolutionWuWindows N Δ V)
      (fun _ => 1/p.kappa3) (fun _ => 1/p.s) := by
    apply add_nonneg <;> apply sum_nonneg <;> intro d _ <;>
      apply mul_nonneg (Nat.cast_nonneg _) <;>
      exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left (hden N hN2 heven) hx
  dsimp only at hf hr hm ⊢
  linarith

/-- Literal five-cutoff mother unit source, with density produced from its prime output.
This does not multiply a source upper bound by an unproved density assumption. -/
theorem mother_unit_pair_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let W := convolutionWuWindows N Δ V
      let Q := (N : ℝ)^(1/2-δ)
      let a0 := fun d => wuLocalCutoff N δ d p.S
      let a1 := fun d => wuLocalCutoff N δ d p.kappa1
      let a2 := fun d => wuLocalCutoff N δ d p.kappa2
      let a3 := fun d => wuLocalCutoff N δ d p.kappa3
      let b := fun d => wuLocalCutoff N δ d p.s
      FourPrimeUnit.source N W a0 a1 a2 a3 b word20 +
        FourPrimeUnit.source N W a0 a1 a2 a3 b word21 ≤
        (HighUnit.boxedSigma20 N δ W (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s) +
          HighUnit.boxedSigma21 N δ W (fun _ => 1/p.kappa3) (fun _ => 1/p.s)) *
          (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
            wuSingularSeries N / log N) + ε*boxTheta N Q W := by
  obtain ⟨T,hT,hd⟩ := mother_envelope_pair_density k hδ hδhi hρ hε
  refine ⟨T,hT,?_⟩
  intro N hN heven i Δ V hb p hp hs
  have hN2 : 2 ≤ N := by have := hT.trans hN; omega
  exact (HighUnitPrimeOutput.mother_unit_pair_filtered hN2 hδ hδhi hb p hp hs).trans
    (hd N hN heven i Δ V hb p hp hs)

end Wu2008DoubleSieve.HighUnitSieve
