import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeSourceKQuadrature

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset Real Filter
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- Each word is paid with the original sigma and reciprocal mass. -/
theorem sourceClosedKMass_uniform (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ j : Fin 4,
        |sourceClosedKMass N δ Δ V p j - sourceLegalKMass N δ Δ V p j| ≤
        epsilon * ((N:ℝ)/log N) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have heta := wuLocalExponent_pos k hδ hδhi
  obtain ⟨T, hT4, hT⟩ := sourceClosedK_uniform k hδ hδhi (mul_pos he heta)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs j
  have hN2 : 2 ≤ N := by omega
  let W := convolutionWuWindows N Δ V
  let w := fun d : ℕ => (convolutionCoeff W d : ℝ) *
    ((N:ℝ)/d/log ((N:ℝ)^(1/2-δ)/d))
  let E := fun d => sourceClosedK N d δ p j - sourceLegalK N d δ p j
  have hid : sourceClosedKMass N δ Δ V p j - sourceLegalKMass N δ Δ V p j =
      ∑ d ∈ boxConvolutionSupport W, w d * E d := by
    unfold sourceClosedKMass sourceLegalKMass HighSourcePayload.mass
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    dsimp only [w, E, W]
    ring
  rw [hid]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, |w d * E d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ boxConvolutionSupport W,
        epsilon * ((N:ℝ)/log N) * ((convolutionCoeff W d : ℝ)/d) := by
      apply sum_le_sum
      intro d hd
      have hg := omega3XPhi_source_bounds hN2 hδ hδhi hb hd
      have hlog := log_pos hg.2.1
      have hw : 0 ≤ w d := by dsimp only [w]; positivity
      have hE : |E d| ≤ epsilon * wuLocalExponent k δ :=
        (hT N hN i Δ V hb p hp hs d hd j).le
      have hscale := omega3X_log_scale_error_le hN2 hδ hδhi hb hd he.le
      calc
        _ = w d * |E d| := by rw [abs_mul, abs_of_nonneg hw]
        _ ≤ w d * (epsilon * wuLocalExponent k δ) :=
          mul_le_mul_of_nonneg_left hE hw
        _ = (convolutionCoeff W d : ℝ) *
            ((N:ℝ) / ((d:ℝ) * log ((N:ℝ)^(1/2-δ)/d)) *
              (epsilon * wuLocalExponent k δ)) := by dsimp only [w]; ring
        _ ≤ (convolutionCoeff W d : ℝ) * (epsilon * ((N:ℝ)/log N) / d) :=
          mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [← mul_sum]; rfl

/-- A single budget controls the sum of absolute word errors, hence each word and all four. -/
theorem sourceClosedKMass_four_uniform (k : ℕ) {δ epsilon : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
        (∀ j : Fin 4,
          |sourceClosedKMass N δ Δ V p j - sourceLegalKMass N δ Δ V p j| ≤
          epsilon * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) ∧
        (∑ j : Fin 4, |sourceClosedKMass N δ Δ V p j - sourceLegalKMass N δ Δ V p j|) ≤
          epsilon * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) ∧
        |(∑ j : Fin 4, sourceClosedKMass N δ Δ V p j) -
          (∑ j : Fin 4, sourceLegalKMass N δ Δ V p j)| ≤
          epsilon * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, hT⟩ := sourceClosedKMass_uniform k hδ hδhi
    (show 0 < epsilon/4 by positivity)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  have h := hT N hN i Δ V hb p hp hs
  have hsum : (∑ j : Fin 4,
      |sourceClosedKMass N δ Δ V p j - sourceLegalKMass N δ Δ V p j|) ≤
      epsilon * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    calc
      _ ≤ ∑ _j : Fin 4, (epsilon/4) * ((N:ℝ)/log N) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
        sum_le_sum fun j _ => h j
      _ = _ := by simp; ring
  refine ⟨fun j => (single_le_sum (fun _ _ => abs_nonneg _) (mem_univ j)).trans hsum,
    hsum, ?_⟩
  rw [← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans hsum

/-- Algebraic payment at the actual varying singular series and original source mass.
This helper is not the quadrature endpoint: the endpoint below supplies its error internally. -/
theorem source_error_theta_payment {k N i : ℕ} {δ Δ epsilon A E : ℝ}
    {V : Fin i → ℝ} (hN4 : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (hA : 0 ≤ A) (he : 0 < epsilon)
    (hE : E ≤ (epsilon/(A+1)) * ((N:ℝ)/log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) :
    A * (wuSingularSeries N / log N) * E ≤
      epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hAp : 0 < A+1 := by positivity
  have he' : 0 < epsilon/(A+1) := div_pos he hAp
  let W := convolutionWuWindows N Δ V
  let Theta := boxTheta N ((N:ℝ)^(1/2-δ)) W
  let X := wuSingularSeries N / log N * ((N:ℝ)/log N) *
    boxConvolutionReciprocalMass W
  have hlog : 0 < log (N:ℝ) :=
    log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hmass : 0 ≤ boxConvolutionReciprocalMass W :=
    sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hpay : X ≤ Theta/2 := HighUnitSource.reciprocalMass_theta_payment hN4 hδ hδhi hb
  have hTheta : 0 ≤ Theta := by linarith
  have hbudget : A * (epsilon/(A+1)) ≤ epsilon := by
    rw [← mul_div_assoc, div_le_iff₀ hAp]
    nlinarith
  calc
    _ ≤ A * (wuSingularSeries N / log N) *
        ((epsilon/(A+1)) * ((N:ℝ)/log N) * boxConvolutionReciprocalMass W) :=
      mul_le_mul_of_nonneg_left hE (mul_nonneg hA (div_nonneg hC hlog.le))
    _ = (A * (epsilon/(A+1))) * X := by dsimp only [X]; ring
    _ ≤ (A * (epsilon/(A+1))) * (Theta/2) :=
      mul_le_mul_of_nonneg_left hpay (mul_nonneg hA he'.le)
    _ ≤ epsilon * (Theta/2) := mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ ≤ epsilon * Theta := mul_le_mul_of_nonneg_left (by linarith) he.le

/-- One epsilon-Theta budget pays each word, their absolute-error sum, and all four.
The threshold precedes every source datum. Neither A nor the original mass is divided out. -/
theorem sourceClosedKMass_four_theta (k : ℕ) {δ epsilon A : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hA : 0 ≤ A) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
        (∀ j : Fin 4, A * (wuSingularSeries N / log N) *
          |sourceClosedKMass N δ Δ V p j - sourceLegalKMass N δ Δ V p j| ≤
          epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)) ∧
        A * (wuSingularSeries N / log N) *
          (∑ j : Fin 4, |sourceClosedKMass N δ Δ V p j - sourceLegalKMass N δ Δ V p j|) ≤
          epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ∧
        A * (wuSingularSeries N / log N) *
          |(∑ j : Fin 4, sourceClosedKMass N δ Δ V p j) -
            (∑ j : Fin 4, sourceLegalKMass N δ Δ V p j)| ≤
          epsilon * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, hT⟩ := sourceClosedKMass_four_uniform k hδ hδhi
    (show 0 < epsilon/(A+1) by positivity)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  obtain ⟨hj, hsum, hall⟩ := hT N hN i Δ V hb p hp hs
  exact ⟨fun j => source_error_theta_payment (hT4.trans hN) hδ hδhi hb hA he (hj j),
    source_error_theta_payment (hT4.trans hN) hδ hδhi hb hA he hsum,
    source_error_theta_payment (hT4.trans hN) hδ hδhi hb hA he hall⟩

end Wu2008DoubleSieve.FourPrimeNonunit
