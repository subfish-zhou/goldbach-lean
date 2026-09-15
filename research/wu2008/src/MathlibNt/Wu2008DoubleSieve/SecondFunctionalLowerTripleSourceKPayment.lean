import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleSourceKQuadrature

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.LowerTripleSourceK
open Finset Real
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- Theta/2 is used only on an error; the integral leading term is never replaced. -/
theorem error_theta_payment {k N i : ℕ} {δ Δ epsilon A E : ℝ}
    {V : Fin i → ℝ} (hN4 : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (hA : 0 < A) (he : 0 < epsilon)
    (hE : E ≤ (2*epsilon/A) * ((N:ℝ)/log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) :
    A * (wuSingularSeries N / log N) * E ≤
      epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hlog : 0 < log (N:ℝ) :=
    log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ wuSingularSeries N / log N :=
    div_nonneg (wuSingularSeries_pos N (by omega)).le hlog.le
  have hpay := mul_le_mul_of_nonneg_left
    (HighUnitSource.reciprocalMass_theta_payment hN4 hδ hδhi hb)
    (show 0 ≤ 2*epsilon by positivity)
  calc
    _ ≤ A * (wuSingularSeries N / log N) *
        ((2*epsilon/A) * ((N:ℝ)/log N) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) :=
      mul_le_mul_of_nonneg_left hE (mul_nonneg hA.le hC)
    _ = (2*epsilon) * (wuSingularSeries N / log N * ((N:ℝ)/log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) := by
      field_simp
    _ ≤ _ := by nlinarith only [hpay]

/-- Full density-scaled comparison with the same actual-phi integral main.
The raw budget 2*epsilon/A is supplied internally before all source data. -/
theorem closedKMass_six_theta (k : ℕ) {δ epsilon A : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hA : 0 < A) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
        (∀ j : Fin 6,
          A * (wuSingularSeries N / log N) * closedKMass N δ Δ V p j ≤
          A * (wuSingularSeries N / log N) * integralKMass N δ Δ V p j +
          epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) ∧
        A * (wuSingularSeries N / log N) * (∑ j : Fin 6, closedKMass N δ Δ V p j) ≤
          A * (wuSingularSeries N / log N) * (∑ j : Fin 6, integralKMass N δ Δ V p j) +
          epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := closedKMass_six_abs_uniform k hδ hδhi
    (show 0 < 2*epsilon/A by positivity)
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb p hp hs
  obtain ⟨hj,_,ha⟩ := hT N hN i Δ V hb p hp hs
  have hN4 := hT4.trans hN
  have hC : 0 ≤ A * (wuSingularSeries N / log N) := mul_nonneg hA.le
    (div_nonneg (wuSingularSeries_pos N (by omega)).le
      (log_pos (by exact_mod_cast (show 1 < N by omega))).le)
  have join (x y : ℝ)
      (h : |x-y| ≤ (2*epsilon/A) * ((N:ℝ)/log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) :
      A * (wuSingularSeries N / log N) * x ≤
        A * (wuSingularSeries N / log N) * y +
        epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
    have hpay := error_theta_payment hN4 hδ hδhi hb hA he h
    have hle := mul_le_mul_of_nonneg_left (le_abs_self (x-y)) hC
    rw [mul_sub] at hle
    linarith only [hpay,hle]
  exact ⟨fun j => join _ _ (hj j), join _ _ ha⟩

/-- Actual rho-dependent lower-triple density coefficient, unchanged on both mains. -/
theorem closedKMass_six_density (k : ℕ) {δ ρ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*
        wuSingularSeries N/log N
      let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)
      (∀ j : Fin 6, closedKMass N δ Δ V p j * A ≤
        integralKMass N δ Δ V p j * A + epsilon*Θ) ∧
      (∑ j : Fin 6, closedKMass N δ Δ V p j) * A ≤
        (∑ j : Fin 6, integralKMass N δ Δ V p j) * A + epsilon*Θ := by
  let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))
  have hA : 0 < A := mul_pos (mul_pos (by linarith)
    (by positivity)) (div_pos (by norm_num) (by linarith))
  obtain ⟨T,hT4,hT⟩ := closedKMass_six_theta k hδ hδhi hA he
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb p hp hs
  simpa only [A, mul_div_assoc, mul_comm] using hT N hN i Δ V hb p hp hs

end Wu2008DoubleSieve.LowerTripleSourceK
